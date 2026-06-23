//! First-class `QF_ABV` solving by eager array elimination (ADR-0010).
//!
//! [`check_with_array_elimination`] is the consumer-facing entry point for
//! queries that use `select`/`store`: it eagerly eliminates arrays to `QF_BV`,
//! solves the result with any [`SolverBackend`], and on `sat` projects the
//! model back to array values and replays it against the original array
//! assertions with the ground evaluator. Pure `QF_BV` queries pass straight
//! through unchanged.

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use axeyum_ir::{
    ArrayValue, Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval,
};
use axeyum_rewrite::{ArrayElimError, ArrayElimination, eliminate_arrays};

use crate::backend::{
    CheckResult, SolverBackend, SolverConfig, SolverError, UnknownKind, UnknownReason,
};
use crate::model::Model;

/// Checks a (possibly array-using) `QF_ABV` conjunction with `backend`.
///
/// Arrays are eliminated to `QF_BV` by read-over-write + Ackermann reduction;
/// a `sat` model is projected back to array values and replayed against the
/// original assertions, so the returned [`Model`] is over the original query.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for array constructs outside the
/// supported fragment (e.g. array equality), or [`SolverError`] from the
/// backend. A `sat` model that fails to replay is a [`SolverError::Backend`].
pub fn check_with_array_elimination<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let elimination = eliminate_arrays(arena, assertions).map_err(map_elim_error)?;
    let eliminated = elimination.assertions().to_vec();
    let result = backend.check(arena, &eliminated, config)?;

    let CheckResult::Sat(model) = result else {
        return Ok(result);
    };

    project_replay_build(arena, &elimination, assertions, &model.to_assignment())
}

/// Lazy/on-demand select-congruence for `QF_ABV` (Track 2, P2.2): read-over-write
/// is applied eagerly (stores are eliminated up front), but each `select` over an
/// array variable is abstracted as a fresh `BitVec` variable and the
/// select-consistency lemma `(i = j) => select(a, i) = select(a, j)` is added ONLY
/// for a select pair (on the same array) that a candidate model actually violates
/// (equal index, unequal results), re-solving until the model is select-consistent
/// or the abstraction is UNSAT.
///
/// This is a CEGAR refinement of the eager [`check_with_array_elimination`]: it
/// starts from the abstraction (the relaxation with no congruence lemmas) and
/// refines only on observed violations. A `select` is just an application of a
/// per-array read function, so this mirrors the lazy Ackermann for uninterpreted
/// functions ([`crate::check_qf_ufbv_lazy`]) with a single index in place of an
/// argument tuple. The abstraction is a relaxation (strictly fewer constraints),
/// so an UNSAT abstraction soundly witnesses UNSAT of the original; a
/// select-consistent `sat` model projects, replays, and is returned over the
/// original query exactly as in the eager path.
///
/// Termination: there are finitely many select pairs and each lemma is added at
/// most once (tracked by index pair), so the loop adds at most `O(selects²)`
/// lemmas before either deciding UNSAT or returning a consistent model.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for array constructs outside the supported
/// `QF_ABV` fragment, or [`SolverError`] from the backend. A consistent `sat`
/// model that fails to replay against the original assertions is a
/// [`SolverError::Backend`].
pub fn check_qf_abv_lazy<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let elim = eliminate_arrays(arena, assertions).map_err(map_elim_error)?;
    if !elim.had_arrays() {
        // No array constructs: nothing to abstract, solve directly.
        return backend.check(arena, assertions, config);
    }

    // The select metadata references `arena`-held index terms; snapshot it into
    // owned data (the index `TermId` is `Copy`) before mutating `arena` with
    // lemmas.
    let selects: Vec<(SymbolId, TermId, SymbolId)> = elim.selects();

    // Group select indices by array symbol, preserving discovery order (linear
    // find — no hash-map iteration in any output).
    let mut groups: Vec<(SymbolId, Vec<usize>)> = Vec::new();
    for (idx, (array, _index, _fresh)) in selects.iter().enumerate() {
        if let Some((_, members)) = groups.iter_mut().find(|(a, _)| a == array) {
            members.push(idx);
        } else {
            groups.push((*array, vec![idx]));
        }
    }

    let mut working = elim.abstraction().to_vec();
    // Index pairs whose congruence lemma has already been asserted; bounds the
    // loop and prevents re-adding the same lemma.
    let mut added: HashSet<(usize, usize)> = HashSet::new();

    loop {
        let assignment = match backend.check(arena, &working, config)? {
            // The abstraction is a relaxation; its UNSAT implies the original's.
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(reason) => return Ok(CheckResult::Unknown(reason)),
            CheckResult::Sat(model) => model.to_assignment(),
        };

        // Collect every newly-violated pair before mutating the arena, so the
        // `assignment` borrow does not collide with the IR builders.
        let mut new_lemmas: Vec<(usize, usize)> = Vec::new();
        for (_array, members) in &groups {
            for a in 0..members.len() {
                for b in (a + 1)..members.len() {
                    let i = members[a];
                    let j = members[b];
                    if added.contains(&(i, j)) {
                        continue;
                    }
                    let (_ai, index_i, fresh_i) = selects[i];
                    let (_aj, index_j, fresh_j) = selects[j];
                    if indices_equal(arena, index_i, index_j, &assignment)?
                        && results_differ(&assignment, fresh_i, fresh_j)
                    {
                        new_lemmas.push((i, j));
                    }
                }
            }
        }

        if new_lemmas.is_empty() {
            // Model is select-consistent: project, replay, and return.
            return project_replay_build(arena, &elim, assertions, &assignment);
        }

        for (i, j) in new_lemmas {
            let lemma = select_congruence_lemma(
                arena,
                selects[i].1,
                selects[j].1,
                selects[i].2,
                selects[j].2,
            )?;
            working.push(lemma);
            added.insert((i, j));
        }
    }
}

/// Projects a candidate model back to array values, replays it against the
/// original `assertions`, and builds the output [`Model`] over the original query
/// (dropping the internal fresh `!arr_sel_*` variables) — the shared `sat` tail of
/// both the eager and lazy entry points.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] if model projection fails or if any original
/// assertion fails to replay to `true` under the projected model.
fn project_replay_build(
    arena: &TermArena,
    elimination: &ArrayElimination,
    assertions: &[TermId],
    assignment: &Assignment,
) -> Result<CheckResult, SolverError> {
    let projected = elimination
        .project_model(arena, assignment)
        .map_err(|error| SolverError::Backend(format!("array model projection failed: {error}")))?;

    for &assertion in assertions {
        match eval(arena, assertion, &projected) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Err(SolverError::Backend(format!(
                    "array sat model replay failed: assertion #{} evaluated to false",
                    assertion.index()
                )));
            }
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "array sat model replay failed: assertion #{} evaluated to non-Boolean {value}",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "array sat model replay failed: assertion #{} failed evaluation: {error}",
                    assertion.index()
                )));
            }
        }
    }

    // Build a model over the original query symbols (drop the internal fresh
    // select variables introduced by elimination).
    let mut out = Model::new();
    for (symbol, name, _sort) in arena.symbols() {
        if name.starts_with("!arr_sel_") {
            continue;
        }
        if let Some(value) = projected.get(symbol) {
            out.set(symbol, value);
        }
    }
    Ok(CheckResult::Sat(out))
}

/// Whether two select index terms evaluate to the same scalar code under
/// `assignment`.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] if an index term fails to evaluate.
fn indices_equal(
    arena: &TermArena,
    index_i: TermId,
    index_j: TermId,
    assignment: &Assignment,
) -> Result<bool, SolverError> {
    let vi = eval(arena, index_i, assignment)
        .map_err(|error| {
            SolverError::Backend(format!("lazy select-congruence eval failed: {error}"))
        })?
        .scalar_code();
    let vj = eval(arena, index_j, assignment)
        .map_err(|error| {
            SolverError::Backend(format!("lazy select-congruence eval failed: {error}"))
        })?
        .scalar_code();
    Ok(vi == vj)
}

/// Whether the two fresh select-result symbols hold different values under
/// `assignment` (an unassigned symbol is treated as a non-match, conservatively
/// no violation).
fn results_differ(assignment: &Assignment, fresh_i: SymbolId, fresh_j: SymbolId) -> bool {
    match (assignment.get(fresh_i), assignment.get(fresh_j)) {
        (Some(vi), Some(vj)) => vi.scalar_code() != vj.scalar_code(),
        _ => false,
    }
}

/// Builds the select-consistency lemma `(index_i = index_j) => (fresh_i =
/// fresh_j)` over the fresh result symbols of two selects on the same array — the
/// single-index analogue of the function-congruence lemma.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] if an IR builder fails.
fn select_congruence_lemma(
    arena: &mut TermArena,
    index_i: TermId,
    index_j: TermId,
    fresh_i: SymbolId,
    fresh_j: SymbolId,
) -> Result<TermId, SolverError> {
    let same_index = arena.eq(index_i, index_j).map_err(|error| {
        SolverError::Backend(format!("lazy select-congruence build failed: {error}"))
    })?;
    let var_i = arena.var(fresh_i);
    let var_j = arena.var(fresh_j);
    let same_result = arena.eq(var_i, var_j).map_err(|error| {
        SolverError::Backend(format!("lazy select-congruence build failed: {error}"))
    })?;
    arena.implies(same_index, same_result).map_err(|error| {
        SolverError::Backend(format!("lazy select-congruence build failed: {error}"))
    })
}

fn map_elim_error(error: ArrayElimError) -> SolverError {
    match error {
        ArrayElimError::Unsupported(what) => SolverError::Unsupported(what),
        ArrayElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    }
}

/// Deterministic bound on the on-demand read-over-write (ROW) refinement rounds
/// before the lazy-ROW path returns `unknown`. Each round adds at least one exact
/// ROW lemma (or terminates), so a blow-up degrades gracefully rather than
/// looping or exhausting memory.
const MAX_ROW_ROUNDS: usize = 64;

/// Deterministic bound on the number of distinct `select`/store-resolution sites
/// the lazy-ROW abstraction will materialise. A query that would create more than
/// this many sites (deeply nested stores fanned out over many reads) declines to
/// `unknown` rather than risk an unbounded blow-up.
const MAX_ROW_SITES: usize = 4096;

/// Builds the `unknown` result with the lazy-ROW resource-limit classification.
fn row_unknown(detail: String) -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::ResourceLimit,
        detail,
    })
}

/// Whether `deadline` (if set) has passed.
fn past_deadline(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|d| Instant::now() >= d)
}

/// Decides a `QF_ABV` query with `store` over a **wide index** by adding the
/// read-over-write (ROW) axiom **on demand** (CEGAR), instead of eagerly
/// enumerating index equalities the way bounded extensionality / Ackermann
/// pairing does.
///
/// This is strictly additive coverage over [`check_qf_abv_lazy`]:
///
/// * If the eager elimination ([`eliminate_arrays`]) accepts the query (every
///   small-index shape it already decides, and the plain wide-index
///   `select(store(…))` cases whose `ite` chain it resolves without enumeration),
///   this delegates to [`check_qf_abv_lazy`] verbatim — the verdict is unchanged.
/// * Only when eager elimination **refuses** (`Unsupported`) — the canonical case
///   being a wide-index *array equality involving a store*, `b = store(a, i, v)`,
///   which bounded extensionality declines above its 8-bit index cap — does the
///   lazy-ROW path engage.
///
/// # The lazy-ROW procedure
///
/// 1. **Array-definition substitution.** Each top-level assertion `v = E` (or
///    `E = v`) with `v` an array *variable* is inlined as a substitution `v := E`
///    (sound: equal arrays are interchangeable), removing the array equality. A
///    surviving array equality between two terms neither of which is a substitutable
///    variable (true extensionality, which a finite lazy lemma set cannot decide
///    for `sat`) makes the path **decline** (`unknown`) — never a wrong verdict.
/// 2. **Abstraction.** Every maximal `select(…)` term is replaced by a fresh
///    `BitVec` variable, yielding an array-free `QF_BV` relaxation. For a select
///    over a store, the *inner* select `select(base', index)` is materialised as a
///    site too, so the ROW axiom can chain to it.
/// 3. **CEGAR.** The relaxation is solved. `unsat` of the relaxation soundly
///    transfers (it has strictly fewer constraints), `unknown` propagates. On a
///    `sat` candidate, every site's ROW axiom (and read-over-read congruence for
///    base-variable selects) is checked against the model; each **violated**
///    instance is an exact, valid lemma that is added and the relaxation re-solved.
///    When no instance is violated, the candidate is **projected and replayed**
///    against the *original* assertions with the ground evaluator (accepted only if
///    it genuinely satisfies them).
///
/// Bounded by `MAX_ROW_ROUNDS`, `MAX_ROW_SITES` and the optional
/// `config.timeout` deadline; any blow-up degrades to `unknown`.
///
/// # Errors
///
/// Returns [`SolverError`] from the backend. A consistent `sat` candidate that
/// fails to replay against the original assertions is a [`SolverError::Backend`].
pub fn check_qf_abv_lazy_row<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // If the eager elimination accepts the query, it (or the existing lazy
    // select-congruence path built on it) already decides it — delegate and never
    // change a decided verdict.
    match eliminate_arrays(arena, assertions) {
        Ok(_) => return check_qf_abv_lazy(backend, arena, assertions, config),
        Err(ArrayElimError::Ir(inner)) => return Err(SolverError::Backend(inner.to_string())),
        // The refused case: engage the lazy-ROW path below.
        Err(ArrayElimError::Unsupported(_)) => {}
    }

    // Step 1: inline array-variable definitions `v = E`, removing array equalities.
    // A surviving (non-substitutable) array equality is a *true extensionality*
    // case: hand it to the lazy-extensionality CEGAR path (diff-skolem witnesses +
    // on-demand select-congruence) instead of declining.
    let Some((substituted, defs)) = substitute_array_definitions(arena, assertions)? else {
        return check_qf_abv_lazy_ext(backend, arena, assertions, config);
    };

    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    let replay = ReplayTargets {
        originals: assertions,
        defs: &defs,
    };
    check_row_cegar(backend, arena, &substituted, &replay, config, deadline)
}

/// A map from a defined array variable to its definition body term.
type ArrayDefs = HashMap<SymbolId, TermId>;

/// Inlines every top-level array-variable definition `v = E` (or `E = v`) as the
/// substitution `v := E`, returning the rewritten assertions with the definitional
/// equalities dropped. Returns `None` if any array equality cannot be turned into
/// such a substitution (so the caller declines soundly).
fn substitute_array_definitions(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Option<(Vec<TermId>, ArrayDefs)>, SolverError> {
    // Collect definitions `v := E`. A variable defined more than once, or defined
    // in terms of itself (directly), is not inlined here — decline.
    let mut defs: HashMap<SymbolId, TermId> = HashMap::new();
    let mut definition_terms: HashSet<TermId> = HashSet::new();
    for &assertion in assertions {
        if let TermNode::App { op: Op::Eq, args } = arena.node(assertion) {
            let (lhs, rhs) = (args[0], args[1]);
            if matches!(arena.sort_of(lhs), Sort::Array { .. }) {
                // An array equality: try to read it as a variable definition.
                let def = array_var_symbol(arena, lhs)
                    .map(|s| (s, rhs))
                    .or_else(|| array_var_symbol(arena, rhs).map(|s| (s, lhs)));
                match def {
                    Some((sym, body))
                        if !defs.contains_key(&sym) && !mentions_symbol(arena, body, sym) =>
                    {
                        defs.insert(sym, body);
                        definition_terms.insert(assertion);
                    }
                    // Two-variable equality, repeated/recursive definition, or
                    // structural array equality: cannot inline soundly here.
                    _ => return Ok(None),
                }
            }
        }
    }

    if defs.is_empty() {
        // No array equalities at all (the refusal came from a non-equality shape
        // the lazy path also cannot model) — decline.
        return Ok(None);
    }

    // Apply substitutions to a fixpoint (a definition body may mention another
    // defined variable). Bounded by the number of definitions.
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        if definition_terms.contains(&assertion) {
            continue;
        }
        let Some(rewritten) = apply_array_substitution(arena, assertion, &defs, &mut memo, 0)?
        else {
            return Ok(None);
        };
        out.push(rewritten);
    }
    Ok(Some((out, defs)))
}

/// The symbol behind an array-sorted *variable* term, if `term` is exactly a
/// symbol of array sort.
fn array_var_symbol(arena: &TermArena, term: TermId) -> Option<SymbolId> {
    match arena.node(term) {
        TermNode::Symbol(sym) if matches!(arena.sort_of(term), Sort::Array { .. }) => Some(*sym),
        _ => None,
    }
}

/// Whether `term` mentions `sym` anywhere in its subterm DAG.
fn mentions_symbol(arena: &TermArena, term: TermId, sym: SymbolId) -> bool {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(s) if *s == sym => return true,
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    false
}

/// Rewrites `term`, replacing each array-variable use by its definition body, to a
/// fixpoint. Bounded recursion depth; returns `None` on a definition cycle (depth
/// blow-up) so the caller declines.
fn apply_array_substitution(
    arena: &mut TermArena,
    term: TermId,
    defs: &HashMap<SymbolId, TermId>,
    memo: &mut HashMap<TermId, TermId>,
    depth: usize,
) -> Result<Option<TermId>, SolverError> {
    if depth > defs.len() + 1 {
        // More substitution depth than definitions: a cycle. Decline.
        return Ok(None);
    }
    if let Some(&cached) = memo.get(&term) {
        return Ok(Some(cached));
    }
    let node = arena.node(term).clone();
    let result = match node {
        TermNode::Symbol(sym) => {
            if let Some(&body) = defs.get(&sym) {
                // Recurse into the body (which may use another defined variable).
                let Some(t) = apply_array_substitution(arena, body, defs, memo, depth + 1)? else {
                    return Ok(None);
                };
                t
            } else {
                term
            }
        }
        TermNode::App { op, args } => {
            let mut new_args = Vec::with_capacity(args.len());
            for arg in args {
                let Some(t) = apply_array_substitution(arena, arg, defs, memo, depth)? else {
                    return Ok(None);
                };
                new_args.push(t);
            }
            rebuild_app(arena, op, &new_args)?
        }
        _ => term,
    };
    memo.insert(term, result);
    Ok(Some(result))
}

/// Rebuilds an application from rewritten arguments via the shared typed builder
/// so the result is interned and re-sorted exactly.
fn rebuild_app(arena: &mut TermArena, op: Op, args: &[TermId]) -> Result<TermId, SolverError> {
    axeyum_rewrite::build_app(arena, op, args)
        .map_err(|e| SolverError::Backend(format!("lazy-ROW rebuild failed: {e}")))
}

/// One materialised `select(base, index)` abstraction site.
#[derive(Clone)]
struct RowSite {
    /// The fresh `BitVec` variable that abstracts this read's result.
    fresh: SymbolId,
    /// The (already-rewritten) index term.
    index: TermId,
    /// How the read resolves: a store (ROW), a variable, or a constant array.
    kind: RowKind,
}

/// How an abstracted read resolves under the read-over-write axiom.
#[derive(Clone)]
enum RowKind {
    /// `select(store(_, store_index, store_elem), index)`; `inner` is the site
    /// index of `select(base', index)`.
    Store {
        store_index: TermId,
        store_elem: TermId,
        inner: usize,
    },
    /// `select(v, index)` for an array variable `v`.
    Var { array: SymbolId },
    /// `select((as const _) value, index)`.
    Const { value: TermId },
}

/// One abstracted array (dis)equality atom `a = b` between two array-sorted
/// terms (neither necessarily an inlinable variable definition). The atom is
/// replaced in the abstraction by `flag` (a fresh `Bool` variable); the
/// extensionality CEGAR then constrains `flag` against the array operands on
/// demand (select-congruence when `flag` is true, a diff-skolem witness when
/// `flag` is false).
#[derive(Clone)]
struct ArrayEqAtom {
    /// The fresh `Bool` variable abstracting this `a = b` atom.
    flag: SymbolId,
    /// The (already index-abstracted-free) left array operand term.
    lhs: TermId,
    /// The right array operand term.
    rhs: TermId,
    /// Whether the diff-skolem witness for the `a != b` case has been
    /// materialised yet (at most one per atom).
    diff_materialised: bool,
}

/// The lazy-ROW CEGAR state: the materialised sites and the abstraction builder's
/// memo (so an identical `select(base, index)` maps to a single site/fresh var).
#[derive(Default)]
struct RowCtx {
    sites: Vec<RowSite>,
    /// `(base term, index term) -> site index`.
    memo: HashMap<(TermId, TermId), usize>,
    fresh_counter: usize,
    /// Abstracted array (dis)equality atoms, for the lazy-extensionality path.
    eq_atoms: Vec<ArrayEqAtom>,
    /// `(lhs term, rhs term) -> eq_atoms index` (order-insensitive: stored with
    /// the smaller `TermId` first) so an identical array equality maps to one flag.
    eq_memo: HashMap<(TermId, TermId), usize>,
}

impl RowCtx {
    /// Abstracts `term`, replacing each `select(…)` by its site's fresh variable.
    fn abstract_term(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
    ) -> Result<Option<TermId>, SolverError> {
        let node = arena.node(term).clone();
        match node {
            TermNode::App {
                op: Op::Select,
                args,
            } => {
                let Some(index) = self.abstract_term(arena, args[1])? else {
                    return Ok(None);
                };
                // `select((as const _) v, j)` is `v` for every `j` — fold it
                // directly rather than materialising an unconstrained site.
                if let TermNode::App {
                    op: Op::ConstArray { .. },
                    args: const_args,
                } = arena.node(args[0]).clone()
                {
                    return self.abstract_term(arena, const_args[0]);
                }
                let Some(site) = self.resolve_select(arena, args[0], index)? else {
                    return Ok(None);
                };
                Ok(Some(arena.var(self.sites[site].fresh)))
            }
            TermNode::App { op: Op::Store, .. } => {
                // A bare store in a non-select position cannot be abstracted to a
                // scalar; decline.
                Ok(None)
            }
            TermNode::App { op, args } => {
                let mut new_args = Vec::with_capacity(args.len());
                for arg in args {
                    let Some(t) = self.abstract_term(arena, arg)? else {
                        return Ok(None);
                    };
                    new_args.push(t);
                }
                Ok(Some(rebuild_app(arena, op, &new_args)?))
            }
            _ => Ok(Some(term)),
        }
    }

    /// Materialises (or reuses) the site for `select(base, index)` with `index`
    /// already abstracted, returning its site index. `None` declines an
    /// unmodellable base shape.
    fn resolve_select(
        &mut self,
        arena: &mut TermArena,
        base: TermId,
        index: TermId,
    ) -> Result<Option<usize>, SolverError> {
        if let Some(&site) = self.memo.get(&(base, index)) {
            return Ok(Some(site));
        }
        if self.sites.len() >= MAX_ROW_SITES {
            return Ok(None);
        }
        let Some((_, element_width)) = arena.sort_of(base).array_widths() else {
            return Ok(None);
        };
        let node = arena.node(base).clone();
        let kind = match node {
            TermNode::App {
                op: Op::Store,
                args,
            } => {
                let Some(store_index) = self.abstract_term(arena, args[1])? else {
                    return Ok(None);
                };
                let Some(store_elem) = self.abstract_term(arena, args[2])? else {
                    return Ok(None);
                };
                let Some(inner) = self.resolve_select(arena, args[0], index)? else {
                    return Ok(None);
                };
                RowKind::Store {
                    store_index,
                    store_elem,
                    inner,
                }
            }
            TermNode::Symbol(sym) if matches!(arena.sort_of(base), Sort::Array { .. }) => {
                RowKind::Var { array: sym }
            }
            TermNode::App {
                op: Op::ConstArray { .. },
                args,
            } => {
                let Some(value) = self.abstract_term(arena, args[0])? else {
                    return Ok(None);
                };
                RowKind::Const { value }
            }
            // `select` over an `ite` of arrays, or any other base, is outside the
            // modelled fragment — decline.
            _ => return Ok(None),
        };
        let fresh = self.fresh_symbol(arena, element_width)?;
        let site = self.sites.len();
        self.sites.push(RowSite { fresh, index, kind });
        self.memo.insert((base, index), site);
        Ok(Some(site))
    }

    fn fresh_symbol(&mut self, arena: &mut TermArena, width: u32) -> Result<SymbolId, SolverError> {
        let name = format!("!row_sel_{}", self.fresh_counter);
        self.fresh_counter += 1;
        arena
            .declare(&name, Sort::BitVec(width))
            .map_err(|e| SolverError::Backend(format!("lazy-ROW fresh symbol failed: {e}")))
    }

    /// Abstracts `term` like [`Self::abstract_term`], but additionally replaces
    /// each **array (dis)equality atom** `a = b` (an `Op::Eq` whose operands are
    /// array-sorted) by a fresh `Bool` flag variable, recording the operands for
    /// the lazy-extensionality CEGAR. This is strictly a superset of
    /// [`Self::abstract_term`]: a query with no array-eq atom abstracts identically.
    fn abstract_with_array_eq(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
    ) -> Result<Option<TermId>, SolverError> {
        if let TermNode::App { op: Op::Eq, args } = arena.node(term).clone() {
            if matches!(arena.sort_of(args[0]), Sort::Array { .. }) {
                let flag = self.array_eq_flag(arena, args[0], args[1])?;
                return Ok(Some(arena.var(flag)));
            }
        }
        let node = arena.node(term).clone();
        match node {
            // Reuse the ROW abstraction for selects/stores/scalars; only the
            // top-level/structural Boolean wrapping needs the array-eq rewrite, so
            // recurse with this method through Boolean/structural apps.
            TermNode::App { op: Op::Select, .. } | TermNode::App { op: Op::Store, .. } => {
                self.abstract_term(arena, term)
            }
            TermNode::App { op, args } => {
                let mut new_args = Vec::with_capacity(args.len());
                for arg in args {
                    let Some(t) = self.abstract_with_array_eq(arena, arg)? else {
                        return Ok(None);
                    };
                    new_args.push(t);
                }
                Ok(Some(rebuild_app(arena, op, &new_args)?))
            }
            _ => Ok(Some(term)),
        }
    }

    /// Returns the index of (materialising if needed) the array-eq atom for
    /// `lhs = rhs`, registering a fresh `Bool` flag. The key is order-insensitive
    /// (`a = b` and `b = a` share a flag).
    fn array_eq_atom(
        &mut self,
        arena: &mut TermArena,
        lhs: TermId,
        rhs: TermId,
    ) -> Result<usize, SolverError> {
        let key = if lhs.index() <= rhs.index() {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };
        if let Some(&idx) = self.eq_memo.get(&key) {
            return Ok(idx);
        }
        let name = format!("!ext_eq_{}", self.fresh_counter);
        self.fresh_counter += 1;
        let flag = arena
            .declare(&name, Sort::Bool)
            .map_err(|e| SolverError::Backend(format!("lazy-ext flag declare failed: {e}")))?;
        let idx = self.eq_atoms.len();
        self.eq_atoms.push(ArrayEqAtom {
            flag,
            lhs: key.0,
            rhs: key.1,
            diff_materialised: false,
        });
        self.eq_memo.insert(key, idx);
        Ok(idx)
    }

    /// The fresh `Bool` flag symbol abstracting the array equality `lhs = rhs`.
    fn array_eq_flag(
        &mut self,
        arena: &mut TermArena,
        lhs: TermId,
        rhs: TermId,
    ) -> Result<SymbolId, SolverError> {
        let idx = self.array_eq_atom(arena, lhs, rhs)?;
        Ok(self.eq_atoms[idx].flag)
    }
}

/// The lazy-ROW CEGAR loop over `substituted` (array-equality-free) assertions,
/// replaying every consistent candidate against the `originals`.
/// The replay targets for a consistent lazy-ROW candidate: the original
/// assertions and the inlined array-variable definitions needed to reconstruct
/// the substituted-away variables.
struct ReplayTargets<'a> {
    originals: &'a [TermId],
    defs: &'a ArrayDefs,
}

fn check_row_cegar<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    substituted: &[TermId],
    replay: &ReplayTargets<'_>,
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<CheckResult, SolverError> {
    let mut ctx = RowCtx::default();
    let mut working: Vec<TermId> = Vec::with_capacity(substituted.len());
    for &assertion in substituted {
        match ctx.abstract_term(arena, assertion)? {
            Some(t) => working.push(t),
            None => {
                return Ok(row_unknown(
                    "lazy-ROW declines: an array read is outside the modelled \
                     store/variable/const-array fragment"
                        .to_owned(),
                ));
            }
        }
    }

    // Const-array reads `select((as const _) v, j) = v` are unconditional facts
    // (one per const-array base site); assert them up front so the fresh var is
    // never left unconstrained on replay.
    let const_lemmas: Vec<(SymbolId, TermId)> = ctx
        .sites
        .iter()
        .filter_map(|site| match &site.kind {
            RowKind::Const { value } => Some((site.fresh, *value)),
            _ => None,
        })
        .collect();
    for (fresh, value) in const_lemmas {
        let var = arena.var(fresh);
        let eqc = arena
            .eq(var, value)
            .map_err(|e| SolverError::Backend(format!("lazy-ROW const lemma failed: {e}")))?;
        working.push(eqc);
    }

    // Lemmas added on demand, tracked so the same instance is never re-added.
    let mut added_row: HashSet<usize> = HashSet::new();
    let mut added_cong: HashSet<(usize, usize)> = HashSet::new();

    for _round in 0..MAX_ROW_ROUNDS {
        if past_deadline(deadline) {
            return Ok(row_unknown(
                "lazy-ROW deadline exceeded before refinement converged".to_owned(),
            ));
        }
        let assignment = match backend.check(arena, &working, config)? {
            // The abstraction is a relaxation; its UNSAT implies the original's.
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(reason) => return Ok(CheckResult::Unknown(reason)),
            CheckResult::Sat(model) => model.to_assignment(),
        };

        // Collect every violated ROW / congruence instance before mutating the
        // arena (the `assignment` borrow must not collide with the IR builders).
        let mut new_row: Vec<usize> = Vec::new();
        for (idx, site) in ctx.sites.iter().enumerate() {
            if added_row.contains(&idx) {
                continue;
            }
            if let RowKind::Store { .. } = site.kind {
                if row_violated(arena, &ctx, idx, &assignment)? {
                    new_row.push(idx);
                }
            }
        }
        // Read-over-read congruence for selects on the same array variable.
        let mut new_cong: Vec<(usize, usize)> = Vec::new();
        for a in 0..ctx.sites.len() {
            for b in (a + 1)..ctx.sites.len() {
                if added_cong.contains(&(a, b)) {
                    continue;
                }
                if let (RowKind::Var { array: va }, RowKind::Var { array: vb }) =
                    (&ctx.sites[a].kind, &ctx.sites[b].kind)
                {
                    if va == vb
                        && indices_equal(
                            arena,
                            ctx.sites[a].index,
                            ctx.sites[b].index,
                            &assignment,
                        )?
                        && results_differ(&assignment, ctx.sites[a].fresh, ctx.sites[b].fresh)
                    {
                        new_cong.push((a, b));
                    }
                }
            }
        }

        if new_row.is_empty() && new_cong.is_empty() {
            // Model is ROW- and congruence-consistent: project, replay, return.
            return project_replay_row(arena, &ctx, replay, &assignment);
        }

        for idx in new_row {
            let lemma = row_axiom_lemma(arena, &ctx, idx)?;
            working.push(lemma);
            added_row.insert(idx);
        }
        for (a, b) in new_cong {
            let lemma = select_congruence_lemma(
                arena,
                ctx.sites[a].index,
                ctx.sites[b].index,
                ctx.sites[a].fresh,
                ctx.sites[b].fresh,
            )?;
            working.push(lemma);
            added_cong.insert((a, b));
        }
    }

    Ok(row_unknown(format!(
        "lazy-ROW refinement did not converge within {MAX_ROW_ROUNDS} rounds"
    )))
}

/// Whether the ROW axiom for store-site `idx` is violated by `assignment`:
/// `select(store(_, I, E), J)` should equal `E` when `J = I` and the inner read's
/// value otherwise.
fn row_violated(
    arena: &TermArena,
    ctx: &RowCtx,
    idx: usize,
    assignment: &Assignment,
) -> Result<bool, SolverError> {
    let site = &ctx.sites[idx];
    let RowKind::Store {
        store_index,
        store_elem,
        inner,
    } = &site.kind
    else {
        return Ok(false);
    };
    let ir = |e: axeyum_ir::IrError| SolverError::Backend(format!("lazy-ROW eval failed: {e}"));
    let j = eval(arena, site.index, assignment)
        .map_err(ir)?
        .scalar_code();
    let i = eval(arena, *store_index, assignment)
        .map_err(ir)?
        .scalar_code();
    let actual = match assignment.get(site.fresh) {
        Some(v) => v.scalar_code(),
        None => return Ok(false),
    };
    let expected = if i == j {
        eval(arena, *store_elem, assignment)
            .map_err(ir)?
            .scalar_code()
    } else {
        match assignment.get(ctx.sites[*inner].fresh) {
            Some(v) => v.scalar_code(),
            None => return Ok(false),
        }
    };
    Ok(actual != expected)
}

/// The symbolic ROW axiom for store-site `idx`:
/// `(J = I → r = E) ∧ (J ≠ I → r = r_inner)`.
fn row_axiom_lemma(arena: &mut TermArena, ctx: &RowCtx, idx: usize) -> Result<TermId, SolverError> {
    let site = ctx.sites[idx].clone();
    let RowKind::Store {
        store_index,
        store_elem,
        inner,
    } = site.kind
    else {
        return Err(SolverError::Backend(
            "lazy-ROW axiom requested for a non-store site".to_owned(),
        ));
    };
    let ir =
        |e: axeyum_ir::IrError| SolverError::Backend(format!("lazy-ROW lemma build failed: {e}"));
    let r = arena.var(site.fresh);
    let r_inner = arena.var(ctx.sites[inner].fresh);
    let same_index = arena.eq(site.index, store_index).map_err(ir)?;
    let r_eq_elem = arena.eq(r, store_elem).map_err(ir)?;
    let r_eq_inner = arena.eq(r, r_inner).map_err(ir)?;
    let hit = arena.implies(same_index, r_eq_elem).map_err(ir)?;
    let not_same = arena.not(same_index).map_err(ir)?;
    let miss = arena.implies(not_same, r_eq_inner).map_err(ir)?;
    arena.and(hit, miss).map_err(ir)
}

/// Projects a consistent lazy-ROW candidate to a model over the original query
/// (reconstructing each array variable's value from its base-variable read sites),
/// replays it against the `originals` with the ground evaluator, and returns it
/// only if it genuinely satisfies every original assertion.
fn project_replay_row(
    arena: &TermArena,
    ctx: &RowCtx,
    replay: &ReplayTargets<'_>,
    assignment: &Assignment,
) -> Result<CheckResult, SolverError> {
    let ir =
        |e: axeyum_ir::IrError| SolverError::Backend(format!("lazy-ROW projection failed: {e}"));
    // Reconstruct array variables from the base-variable read sites only (store
    // reads resolve through the ROW axiom, not a stored array variable).
    let mut arrays: HashMap<SymbolId, Vec<(u128, u128)>> = HashMap::new();
    for site in &ctx.sites {
        if let RowKind::Var { array } = site.kind {
            let index = eval(arena, site.index, assignment)
                .map_err(ir)?
                .scalar_code();
            let value = match assignment.get(site.fresh) {
                Some(v) => v.scalar_code(),
                None => continue,
            };
            arrays.entry(array).or_default().push((index, value));
        }
    }

    let mut projected = assignment.clone();
    for (&array, entries) in &arrays {
        let Some((index_width, element_width)) = arena.symbol(array).1.array_widths() else {
            continue;
        };
        let mut value = ArrayValue::constant(index_width, element_width, 0);
        for &(index, element) in entries {
            value = value.store(index, element);
        }
        projected.set(array, Value::Array(value));
    }

    // Reconstruct the substituted-away defined variables (`v = E`) by evaluating
    // each definition body under the projected model, to a fixpoint over the
    // dependency order (a body may reference another defined variable). The backend
    // model-completes every declared symbol — including these array variables with
    // a placeholder array — so the bodies are recomputed unconditionally (never
    // skipping an already-present placeholder) until the values stabilise. Bounded
    // by the number of definitions.
    for _ in 0..=replay.defs.len() {
        let mut changed = false;
        for (&sym, &body) in replay.defs {
            if let Ok(value @ Value::Array(_)) = eval(arena, body, &projected) {
                if projected.get(sym).as_ref() != Some(&value) {
                    projected.set(sym, value);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Replay against the ORIGINAL assertions: accept only a genuine model.
    for &assertion in replay.originals {
        match eval(arena, assertion, &projected) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Ok(row_unknown(format!(
                    "lazy-ROW candidate failed replay: assertion #{} evaluated to false \
                     (incomplete on this shape)",
                    assertion.index()
                )));
            }
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "lazy-ROW replay: assertion #{} evaluated to non-Boolean {value}",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "lazy-ROW replay: assertion #{} failed evaluation: {error}",
                    assertion.index()
                )));
            }
        }
    }

    let mut out = Model::new();
    for (symbol, name, _sort) in arena.symbols() {
        if name.starts_with("!row_sel_") {
            continue;
        }
        if let Some(value) = projected.get(symbol) {
            out.set(symbol, value);
        }
    }
    Ok(CheckResult::Sat(out))
}

/// Deterministic bound on the number of diff-skolem witnesses the
/// lazy-extensionality path will introduce before declining to `unknown`. Each
/// asserted array disequality needs at most one, so this caps the total number of
/// distinct array (dis)equality atoms whose witness is materialised.
const MAX_DIFF_SKOLEMS: usize = 256;

/// Builds the `unknown` result with the lazy-extensionality classification.
fn ext_unknown(detail: String) -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail,
    })
}

/// Decides a `QF_ABV` query carrying a **true array (dis)equality** — an array
/// equality `a = b` (or its negation) between two array terms *neither* of which
/// is an inlinable variable definition — via **lazy extensionality** (CEGAR):
///
/// * Each array `Op::Eq` atom `a = b` is abstracted to a fresh `Bool` flag.
///   Every `select(…)` is abstracted to a fresh `BitVec` site exactly as in the
///   lazy-ROW path, so ROW / read-over-read congruence are still enforced.
/// * On a candidate model, for each atom: when the flag is **true**, the
///   select-congruence lemma `flag => select(a,i) = select(b,i)` is added for any
///   already-materialised read index `i` that the model leaves inconsistent; when
///   the flag is **false** (`a != b`), a fresh **diff-skolem** index `k` is
///   introduced once and the witness lemma `!flag => select(a,k) != select(b,k)`
///   is added (a concrete index where the arrays differ).
/// * The relaxation's `unsat` transfers (strictly fewer constraints); a
///   refinement-consistent candidate is **projected and replayed** against the
///   *original* assertions — including the array (dis)equalities, re-derived
///   extensionally from the reconstructed array values — and accepted only if it
///   genuinely satisfies them, else `unknown`.
///
/// Strictly additive: any query the eager / lazy-ROW paths already decide reaches
/// this function only after they refuse, so it never changes a decided verdict.
/// Bounded by `MAX_ROW_ROUNDS`, `MAX_ROW_SITES`, `MAX_DIFF_SKOLEMS`, and the
/// optional deadline; a blow-up degrades to `unknown`.
///
/// # Errors
///
/// Returns [`SolverError`] from the backend. A `sat` candidate that fails to
/// replay against the originals declines to `unknown`, never a wrong `sat`.
fn check_qf_abv_lazy_ext<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    let mut ctx = RowCtx::default();

    // Abstract: array-eq atoms -> fresh Bool flags, selects -> fresh BV sites.
    let mut working: Vec<TermId> = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        match ctx.abstract_with_array_eq(arena, assertion)? {
            Some(t) => working.push(t),
            None => {
                return Ok(ext_unknown(
                    "lazy-extensionality declines: an array read/term is outside the modelled \
                     store/variable/const-array fragment"
                        .to_owned(),
                ));
            }
        }
    }

    // No array-eq atom survived abstraction: this is a pure-ROW query the ROW
    // path's own abstraction handles — delegate (it re-abstracts from the
    // originals) rather than duplicate it.
    if ctx.eq_atoms.is_empty() {
        let defs = ArrayDefs::new();
        let replay = ReplayTargets {
            originals: assertions,
            defs: &defs,
        };
        return check_row_cegar(backend, arena, assertions, &replay, config, deadline);
    }

    add_const_lemmas(arena, &ctx, &mut working)?;
    ext_cegar_loop(
        backend, arena, &mut ctx, working, assertions, config, deadline,
    )
}

/// Asserts the unconditional `select((as const _) v, j) = v` facts for every
/// const-array site (shared with the lazy-ROW path).
fn add_const_lemmas(
    arena: &mut TermArena,
    ctx: &RowCtx,
    working: &mut Vec<TermId>,
) -> Result<(), SolverError> {
    let const_lemmas: Vec<(SymbolId, TermId)> = ctx
        .sites
        .iter()
        .filter_map(|site| match &site.kind {
            RowKind::Const { value } => Some((site.fresh, *value)),
            _ => None,
        })
        .collect();
    for (fresh, value) in const_lemmas {
        let var = arena.var(fresh);
        let eqc = arena
            .eq(var, value)
            .map_err(|e| SolverError::Backend(format!("lazy-ext const lemma failed: {e}")))?;
        working.push(eqc);
    }
    Ok(())
}

/// The CEGAR loop for the lazy-extensionality path: solve the abstraction, add any
/// violated ROW / congruence / extensionality lemma, repeat to convergence or the
/// bound.
#[allow(clippy::too_many_arguments)]
fn ext_cegar_loop<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    ctx: &mut RowCtx,
    mut working: Vec<TermId>,
    originals: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<CheckResult, SolverError> {
    let mut added_row: HashSet<usize> = HashSet::new();
    let mut added_cong: HashSet<(usize, usize)> = HashSet::new();
    let mut diff_skolems = 0usize;

    for _round in 0..MAX_ROW_ROUNDS {
        if past_deadline(deadline) {
            return Ok(ext_unknown(
                "lazy-extensionality deadline exceeded before refinement converged".to_owned(),
            ));
        }
        let assignment = match backend.check(arena, &working, config)? {
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(reason) => return Ok(CheckResult::Unknown(reason)),
            CheckResult::Sat(model) => model.to_assignment(),
        };

        let mut progressed = false;

        // 1. ROW + read-over-read congruence on the materialised sites.
        progressed |= refine_row_and_congruence(
            arena,
            ctx,
            &assignment,
            &mut working,
            &mut added_row,
            &mut added_cong,
        )?;

        // 2. Extensionality on the array-eq atoms (congruence when the flag is
        //    true, a fresh diff-skolem witness when it is false).
        progressed |=
            refine_extensionality(arena, ctx, &assignment, &mut working, &mut diff_skolems)?;

        if !progressed {
            return project_replay_ext(arena, ctx, originals, &assignment);
        }
    }

    Ok(ext_unknown(format!(
        "lazy-extensionality refinement did not converge within {MAX_ROW_ROUNDS} rounds"
    )))
}

/// Adds every ROW / read-over-read-congruence lemma the candidate violates,
/// returning whether any lemma was added. Shared shape with the lazy-ROW loop.
fn refine_row_and_congruence(
    arena: &mut TermArena,
    ctx: &RowCtx,
    assignment: &Assignment,
    working: &mut Vec<TermId>,
    added_row: &mut HashSet<usize>,
    added_cong: &mut HashSet<(usize, usize)>,
) -> Result<bool, SolverError> {
    let mut new_row: Vec<usize> = Vec::new();
    for (idx, site) in ctx.sites.iter().enumerate() {
        if added_row.contains(&idx) {
            continue;
        }
        if let RowKind::Store { .. } = site.kind {
            if row_violated(arena, ctx, idx, assignment)? {
                new_row.push(idx);
            }
        }
    }
    let mut new_cong: Vec<(usize, usize)> = Vec::new();
    for a in 0..ctx.sites.len() {
        for b in (a + 1)..ctx.sites.len() {
            if added_cong.contains(&(a, b)) {
                continue;
            }
            if let (RowKind::Var { array: va }, RowKind::Var { array: vb }) =
                (&ctx.sites[a].kind, &ctx.sites[b].kind)
            {
                if va == vb
                    && indices_equal(arena, ctx.sites[a].index, ctx.sites[b].index, assignment)?
                    && results_differ(assignment, ctx.sites[a].fresh, ctx.sites[b].fresh)
                {
                    new_cong.push((a, b));
                }
            }
        }
    }

    let progressed = !new_row.is_empty() || !new_cong.is_empty();
    for idx in new_row {
        let lemma = row_axiom_lemma(arena, ctx, idx)?;
        working.push(lemma);
        added_row.insert(idx);
    }
    for (a, b) in new_cong {
        let lemma = select_congruence_lemma(
            arena,
            ctx.sites[a].index,
            ctx.sites[b].index,
            ctx.sites[a].fresh,
            ctx.sites[b].fresh,
        )?;
        working.push(lemma);
        added_cong.insert((a, b));
    }
    Ok(progressed)
}

/// Refines the array (dis)equality atoms against extensionality, returning whether
/// any lemma was added.
///
/// For each atom `a = b` with flag `f` under `assignment`:
/// * `f` **true** but some already-materialised read index `i` has
///   `select(a,i) != select(b,i)` in the model: add `f => select(a,i)=select(b,i)`.
/// * `f` **false** and no diff-witness yet: introduce a fresh diff-skolem `k` and
///   add `!f => select(a,k) != select(b,k)`.
fn refine_extensionality(
    arena: &mut TermArena,
    ctx: &mut RowCtx,
    assignment: &Assignment,
    working: &mut Vec<TermId>,
    diff_skolems: &mut usize,
) -> Result<bool, SolverError> {
    let mut progressed = false;
    for atom_idx in 0..ctx.eq_atoms.len() {
        let flag = ctx.eq_atoms[atom_idx].flag;
        let flag_true = matches!(assignment.get(flag), Some(Value::Bool(true)));
        if flag_true {
            progressed |= refine_eq_congruence(arena, ctx, atom_idx, assignment, working)?;
        } else if !ctx.eq_atoms[atom_idx].diff_materialised {
            if *diff_skolems >= MAX_DIFF_SKOLEMS {
                continue;
            }
            refine_diff_skolem(arena, ctx, atom_idx, working)?;
            *diff_skolems += 1;
            progressed = true;
        }
    }
    Ok(progressed)
}

/// For a *true*-flagged atom `a = b`, adds `flag => select(a,i)=select(b,i)` for
/// every read index `i` (already materialised on either operand) the model leaves
/// inconsistent. Returns whether any lemma was added.
fn refine_eq_congruence(
    arena: &mut TermArena,
    ctx: &mut RowCtx,
    atom_idx: usize,
    assignment: &Assignment,
    working: &mut Vec<TermId>,
) -> Result<bool, SolverError> {
    // Gather the distinct index terms already read on either operand.
    let (lhs, rhs, flag) = {
        let atom = &ctx.eq_atoms[atom_idx];
        (atom.lhs, atom.rhs, atom.flag)
    };
    let indices = read_indices_for(ctx, lhs, rhs);
    let mut progressed = false;
    for index in indices {
        let Some(site_a) = ctx.resolve_select(arena, lhs, index)? else {
            continue;
        };
        let Some(site_b) = ctx.resolve_select(arena, rhs, index)? else {
            continue;
        };
        let fa = ctx.sites[site_a].fresh;
        let fb = ctx.sites[site_b].fresh;
        if results_differ(assignment, fa, fb) {
            let var_flag = arena.var(flag);
            let va = arena.var(fa);
            let vb = arena.var(fb);
            let eqr = arena
                .eq(va, vb)
                .map_err(|e| SolverError::Backend(format!("lazy-ext cong build failed: {e}")))?;
            let lemma = arena
                .implies(var_flag, eqr)
                .map_err(|e| SolverError::Backend(format!("lazy-ext cong build failed: {e}")))?;
            working.push(lemma);
            progressed = true;
        }
    }
    Ok(progressed)
}

/// The set of index terms already read (as `select` sites) on `lhs` or `rhs`.
fn read_indices_for(ctx: &RowCtx, lhs: TermId, rhs: TermId) -> Vec<TermId> {
    let mut indices: Vec<TermId> = Vec::new();
    for &(base, index) in ctx.memo.keys() {
        if (base == lhs || base == rhs) && !indices.contains(&index) {
            indices.push(index);
        }
    }
    // Deterministic order independent of hash-map iteration.
    indices.sort_by_key(|t| t.index());
    indices
}

/// For a *false*-flagged atom `a != b`, introduces a fresh diff-skolem index `k`
/// and adds the witness lemma `!flag => select(a,k) != select(b,k)`, materialising
/// the two read sites at `k`.
fn refine_diff_skolem(
    arena: &mut TermArena,
    ctx: &mut RowCtx,
    atom_idx: usize,
    working: &mut Vec<TermId>,
) -> Result<(), SolverError> {
    let (lhs, rhs, flag) = {
        let atom = &ctx.eq_atoms[atom_idx];
        (atom.lhs, atom.rhs, atom.flag)
    };
    let Some((index_width, _)) = arena.sort_of(lhs).array_widths() else {
        return Ok(());
    };
    let name = format!("!ext_diff_{}", ctx.fresh_counter);
    ctx.fresh_counter += 1;
    let k_sym = arena
        .declare(&name, Sort::BitVec(index_width))
        .map_err(|e| SolverError::Backend(format!("lazy-ext diff-skolem declare failed: {e}")))?;
    let k = arena.var(k_sym);

    let Some(site_a) = ctx.resolve_select(arena, lhs, k)? else {
        return Ok(());
    };
    let Some(site_b) = ctx.resolve_select(arena, rhs, k)? else {
        return Ok(());
    };
    let fa = ctx.sites[site_a].fresh;
    let fb = ctx.sites[site_b].fresh;
    let var_flag = arena.var(flag);
    let not_flag = arena
        .not(var_flag)
        .map_err(|e| SolverError::Backend(format!("lazy-ext diff build failed: {e}")))?;
    let va = arena.var(fa);
    let vb = arena.var(fb);
    let eqr = arena
        .eq(va, vb)
        .map_err(|e| SolverError::Backend(format!("lazy-ext diff build failed: {e}")))?;
    let ner = arena
        .not(eqr)
        .map_err(|e| SolverError::Backend(format!("lazy-ext diff build failed: {e}")))?;
    let lemma = arena
        .implies(not_flag, ner)
        .map_err(|e| SolverError::Backend(format!("lazy-ext diff build failed: {e}")))?;
    working.push(lemma);
    ctx.eq_atoms[atom_idx].diff_materialised = true;
    Ok(())
}

/// Projects a refinement-consistent lazy-extensionality candidate to a model over
/// the original query (reconstructing each array variable from its base-variable
/// read sites), replays it against the `originals` with the ground evaluator —
/// re-deriving the array (dis)equalities extensionally — and returns it only if it
/// genuinely satisfies every original assertion, else `unknown`.
fn project_replay_ext(
    arena: &TermArena,
    ctx: &RowCtx,
    originals: &[TermId],
    assignment: &Assignment,
) -> Result<CheckResult, SolverError> {
    let ir =
        |e: axeyum_ir::IrError| SolverError::Backend(format!("lazy-ext projection failed: {e}"));
    // Reconstruct array variables from the base-variable read sites only.
    let mut arrays: HashMap<SymbolId, Vec<(u128, u128)>> = HashMap::new();
    for site in &ctx.sites {
        if let RowKind::Var { array } = site.kind {
            let index = eval(arena, site.index, assignment)
                .map_err(ir)?
                .scalar_code();
            let value = match assignment.get(site.fresh) {
                Some(v) => v.scalar_code(),
                None => continue,
            };
            arrays.entry(array).or_default().push((index, value));
        }
    }

    let mut projected = assignment.clone();
    for (&array, entries) in &arrays {
        let Some((index_width, element_width)) = arena.symbol(array).1.array_widths() else {
            continue;
        };
        let mut value = ArrayValue::constant(index_width, element_width, 0);
        for &(index, element) in entries {
            value = value.store(index, element);
        }
        projected.set(array, Value::Array(value));
    }

    // Replay against the ORIGINAL assertions, re-deriving every array (dis)equality
    // extensionally from the reconstructed arrays. Accept only a genuine model;
    // a replay miss (reconstruction underdetermined this shape) declines.
    for &assertion in originals {
        match eval(arena, assertion, &projected) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Ok(ext_unknown(format!(
                    "lazy-extensionality candidate failed replay: assertion #{} evaluated to \
                     false (incomplete on this shape)",
                    assertion.index()
                )));
            }
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "lazy-ext replay: assertion #{} evaluated to non-Boolean {value}",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "lazy-ext replay: assertion #{} failed evaluation: {error}",
                    assertion.index()
                )));
            }
        }
    }

    let mut out = Model::new();
    for (symbol, name, _sort) in arena.symbols() {
        if name.starts_with("!row_sel_")
            || name.starts_with("!ext_eq_")
            || name.starts_with("!ext_diff_")
        {
            continue;
        }
        if let Some(value) = projected.get(symbol) {
            out.set(symbol, value);
        }
    }
    Ok(CheckResult::Sat(out))
}

#[cfg(test)]
#[allow(clippy::many_single_char_names, clippy::similar_names)]
mod tests {
    use super::{check_qf_abv_lazy, check_with_array_elimination};
    use crate::backend::{CheckResult, SolverConfig};
    use crate::sat_bv_backend::SatBvBackend;
    use axeyum_ir::{TermArena, Value, eval};

    #[test]
    fn lazy_abv_refutes_select_congruence() {
        // select(a, i) != select(a, j) AND i = j  =>  UNSAT (a lemma is required
        // to refute: the abstraction alone, with two unconstrained fresh select
        // results, is SAT).
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 3, 4).unwrap();
        let i = arena.bv_var("i", 3).unwrap();
        let j = arena.bv_var("j", 3).unwrap();
        let read_i = arena.select(a, i).unwrap();
        let read_j = arena.select(a, j).unwrap();
        let reads_ne = {
            let eq = arena.eq(read_i, read_j).unwrap();
            arena.not(eq).unwrap()
        };
        let i_eq_j = arena.eq(i, j).unwrap();

        let mut backend = SatBvBackend::new();
        let config = SolverConfig::default();
        let result =
            check_qf_abv_lazy(&mut backend, &mut arena, &[reads_ne, i_eq_j], &config).unwrap();
        assert_eq!(result, CheckResult::Unsat);
    }

    #[test]
    fn lazy_abv_sat_model_replays() {
        // select(store(a, i, v), i) = w AND v = w  =>  SAT. Read-over-write
        // forces select(store(a,i,v),i) = v, so w = v is consistent. The
        // returned model must replay against every original assertion.
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 3, 4).unwrap();
        let i = arena.bv_var("i", 3).unwrap();
        let v = arena.bv_var("v", 4).unwrap();
        let w = arena.bv_var("w", 4).unwrap();
        let stored = arena.store(a, i, v).unwrap();
        let read = arena.select(stored, i).unwrap();
        let read_eq_w = arena.eq(read, w).unwrap();
        let v_eq_w = arena.eq(v, w).unwrap();
        let originals = [read_eq_w, v_eq_w];

        let mut backend = SatBvBackend::new();
        let config = SolverConfig::default();
        let result = check_qf_abv_lazy(&mut backend, &mut arena, &originals, &config).unwrap();
        let CheckResult::Sat(model) = result else {
            panic!("expected SAT, got {result:?}");
        };
        let assignment = model.to_assignment();
        for &t in &originals {
            assert_eq!(
                eval(&arena, t, &assignment).unwrap(),
                Value::Bool(true),
                "original assertion must replay to true"
            );
        }
    }

    #[test]
    fn lazy_abv_matches_eager_differential() {
        // ~200 deterministic-random small QF_ABV formulas; the lazy verdict must
        // agree with the eager array-elimination verdict whenever both decide.
        let config = SolverConfig::default();
        let mut jointly_decided = 0usize;
        let mut unsat_count = 0usize;

        // Simple LCG (no `rand` crate); seeded by a constant, varied per case.
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;

        for _case in 0..200usize {
            let mut arena = TermArena::new();
            let assertions = [build_case(&mut arena, &mut state)];

            let mut lazy_backend = SatBvBackend::new();
            let mut eager_backend = SatBvBackend::new();
            let lazy = check_qf_abv_lazy(&mut lazy_backend, &mut arena, &assertions, &config)
                .expect("lazy check");
            let eager =
                check_with_array_elimination(&mut eager_backend, &mut arena, &assertions, &config)
                    .expect("eager check");

            if let (Some(l), Some(e)) = (verdict(&lazy), verdict(&eager)) {
                assert_eq!(
                    l, e,
                    "lazy/eager disagree on a jointly-decided case (lazy={lazy:?}, eager={eager:?})"
                );
                jointly_decided += 1;
                if !l {
                    unsat_count += 1;
                }
            }
        }

        assert!(
            jointly_decided > 0,
            "expected some jointly-decided cases, got none"
        );
        assert!(
            unsat_count > 0,
            "expected at least one UNSAT case, got none"
        );
    }

    /// Advances a 64-bit LCG and returns a 32-bit draw (no `rand` crate).
    fn next_rand(state: &mut u64) -> u32 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (*state >> 33) as u32
    }

    /// Builds one deterministic-random small `QF_ABV` formula over `BitVec(3)`
    /// indices / `BitVec(4)` elements and 1-2 array variables, returning its
    /// single top-level assertion.
    fn build_case(arena: &mut TermArena, state: &mut u64) -> axeyum_ir::TermId {
        let iw = 3u32;
        let ew = 4u32;
        let a = arena.array_var("a", iw, ew).unwrap();
        let b = arena.array_var("b", iw, ew).unwrap();
        let arrays = [a, b];

        // Index/element pools (scalars).
        let mut idx_pool: Vec<axeyum_ir::TermId> = vec![
            arena.bv_var("i", iw).unwrap(),
            arena.bv_var("j", iw).unwrap(),
            arena.bv_var("k", iw).unwrap(),
        ];
        idx_pool.push(
            arena
                .bv_const(iw, u128::from(next_rand(state) & 0x7))
                .unwrap(),
        );
        let mut elem_pool: Vec<axeyum_ir::TermId> = vec![
            arena.bv_var("v", ew).unwrap(),
            arena.bv_var("w", ew).unwrap(),
        ];
        elem_pool.push(
            arena
                .bv_const(ew, u128::from(next_rand(state) & 0xf))
                .unwrap(),
        );

        // Array pool: variables plus a few stores.
        let mut arr_pool: Vec<axeyum_ir::TermId> = arrays.to_vec();
        for _ in 0..2 {
            let base = arr_pool[(next_rand(state) as usize) % arr_pool.len()];
            let idx = idx_pool[(next_rand(state) as usize) % idx_pool.len()];
            let elem = elem_pool[(next_rand(state) as usize) % elem_pool.len()];
            let stored = arena.store(base, idx, elem).unwrap();
            arr_pool.push(stored);
        }

        // A few selects feed the element pool.
        for _ in 0..3 {
            let arr = arr_pool[(next_rand(state) as usize) % arr_pool.len()];
            let idx = idx_pool[(next_rand(state) as usize) % idx_pool.len()];
            let read = arena.select(arr, idx).unwrap();
            elem_pool.push(read);
        }

        // eq/diseq atoms over the element pool.
        let atom_count = 2 + (next_rand(state) % 3) as usize;
        let mut atoms: Vec<axeyum_ir::TermId> = Vec::with_capacity(atom_count);
        for _ in 0..atom_count {
            let lhs = elem_pool[(next_rand(state) as usize) % elem_pool.len()];
            let rhs = elem_pool[(next_rand(state) as usize) % elem_pool.len()];
            let eq = arena.eq(lhs, rhs).unwrap();
            let atom = if next_rand(state) % 2 == 0 {
                eq
            } else {
                arena.not(eq).unwrap()
            };
            atoms.push(atom);
        }

        // Combine atoms into one formula with and/or, then maybe negate.
        let mut formula = atoms[0];
        for &atom in &atoms[1..] {
            formula = if next_rand(state) % 2 == 0 {
                arena.and(formula, atom).unwrap()
            } else {
                arena.or(formula, atom).unwrap()
            };
        }
        if next_rand(state) % 4 == 0 {
            formula = arena.not(formula).unwrap();
        }
        formula
    }

    /// `Some(true)` for SAT, `Some(false)` for UNSAT, `None` for Unknown — the
    /// shared verdict for differential comparison.
    fn verdict(result: &CheckResult) -> Option<bool> {
        match result {
            CheckResult::Sat(_) => Some(true),
            CheckResult::Unsat => Some(false),
            CheckResult::Unknown(_) => None,
        }
    }
}
