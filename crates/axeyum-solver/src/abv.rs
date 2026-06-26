//! First-class `QF_ABV` solving by eager array elimination (ADR-0010).
//!
//! [`check_with_array_elimination`] is the consumer-facing entry point for
//! queries that use `select`/`store`: it eagerly eliminates arrays to `QF_BV`,
//! solves the result with any [`SolverBackend`], and on `sat` projects the
//! model back to array values and replays it against the original array
//! assertions with the ground evaluator. Pure `QF_BV` queries pass straight
//! through unchanged.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::time::{Duration, Instant};

use axeyum_ir::{
    ArrayValue, Assignment, FuncValue, GenericArrayValue, Op, Sort, SymbolId, TermArena, TermId,
    TermNode, Value, eval, well_founded_default,
};
use axeyum_rewrite::{ArrayElimError, ArrayElimination, eliminate_arrays};

use crate::backend::{
    Capabilities, CheckResult, SolverBackend, SolverConfig, SolverError, UnknownKind, UnknownReason,
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

    project_replay_build(
        arena,
        &elimination,
        assertions,
        &complete_assignment(arena, &model.to_assignment()),
    )
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
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));

    loop {
        if past_deadline(deadline) {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Timeout,
                detail: "lazy select-congruence deadline exceeded before refinement converged"
                    .to_owned(),
            }));
        }
        let round_config = config_with_remaining_deadline(config, deadline);
        let assignment = match backend.check(arena, &working, &round_config)? {
            // The abstraction is a relaxation; its UNSAT implies the original's.
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(reason) => return Ok(CheckResult::Unknown(reason)),
            CheckResult::Sat(model) => complete_assignment(arena, &model.to_assignment()),
        };

        // Collect every newly-violated pair before mutating the arena, so the
        // `assignment` borrow does not collide with the IR builders.
        let mut new_lemmas: Vec<(usize, usize)> = Vec::new();
        for (_array, members) in &groups {
            if past_deadline(deadline) {
                return Ok(CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::Timeout,
                    detail: "lazy select-congruence deadline exceeded while checking pairs"
                        .to_owned(),
                }));
            }
            for a in 0..members.len() {
                for b in (a + 1)..members.len() {
                    if past_deadline(deadline) {
                        return Ok(CheckResult::Unknown(UnknownReason {
                            kind: UnknownKind::Timeout,
                            detail: "lazy select-congruence deadline exceeded while checking pairs"
                                .to_owned(),
                        }));
                    }
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

/// Whether two select index terms evaluate to the same value under `assignment`.
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
    if index_i == index_j {
        return Ok(true);
    }
    let vi = eval(arena, index_i, assignment).map_err(|error| {
        SolverError::Backend(format!("lazy select-congruence eval failed: {error}"))
    })?;
    let vj = eval(arena, index_j, assignment).map_err(|error| {
        SolverError::Backend(format!("lazy select-congruence eval failed: {error}"))
    })?;
    Ok(vi == vj)
}

/// Whether the two fresh select-result symbols hold different values under
/// `assignment` (an unassigned symbol is treated as a non-match, conservatively
/// no violation).
fn results_differ(assignment: &Assignment, fresh_i: SymbolId, fresh_j: SymbolId) -> bool {
    match (assignment.get(fresh_i), assignment.get(fresh_j)) {
        (Some(vi), Some(vj)) => vi != vj,
        _ => false,
    }
}

/// Whether two abstracted scalar read expressions evaluate differently under
/// `assignment`.
fn read_terms_differ(
    arena: &TermArena,
    lhs: TermId,
    rhs: TermId,
    assignment: &Assignment,
) -> Result<bool, SolverError> {
    let ir = |error| SolverError::Backend(format!("lazy-ext read eval failed: {error}"));
    let lhs = eval(arena, lhs, assignment).map_err(ir)?;
    let rhs = eval(arena, rhs, assignment).map_err(ir)?;
    Ok(lhs != rhs)
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
const SCALAR_LOCAL_SEARCH_PROBE_MS: u64 = 100;

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

fn config_with_remaining_deadline(
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> SolverConfig {
    let Some(deadline) = deadline else {
        return config.clone();
    };
    let remaining = deadline
        .checked_duration_since(Instant::now())
        .unwrap_or(Duration::ZERO);
    let mut scoped = config.clone();
    scoped.timeout = Some(match config.timeout {
        Some(existing) => existing.min(remaining),
        None => remaining,
    });
    scoped
}

fn contextual_unknown(
    context: &str,
    round: usize,
    sites: usize,
    row_lemmas: usize,
    cong_lemmas: usize,
    reason: &UnknownReason,
) -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: reason.kind,
        detail: format!(
            "{context} after round {round} (sites={sites}, row_lemmas={row_lemmas}, \
             cong_lemmas={cong_lemmas}): {}",
            reason.detail
        ),
    })
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

/// Decides the scalar linear-arithmetic array slice (currently `Array Int E`
/// with scalar linear-arithmetic/Bool elements) through the same lazy
/// ROW/extensionality CEGAR used for BV arrays, but with the arithmetic DPLL(T)
/// backend as the scalar solver.
///
/// This is intentionally a narrow adapter, not a new array algorithm: every
/// `sat` still projects arrays and replays the original assertions; `unsat` is
/// from an abstraction/refinement formula solved by the scalar backend.
pub fn check_qf_alia_lazy_row(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let mut backend = ArithDpllBackend;
    check_qf_abv_lazy_row(&mut backend, arena, assertions, config)
}

/// Decides the scalar linear-integer + UF array slice through lazy
/// ROW/extensionality CEGAR with the existing `QF_UFLIA` combination as the
/// scalar backend.
///
/// This is deliberately an adapter: array reasoning remains in the CEGAR loop,
/// while the scalar side handles integer arithmetic and UF congruence over the
/// abstracted select/index terms. Every `sat` is still projected and replayed
/// against the original array formula before it is returned.
pub fn check_qf_auflia_lazy_row(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let mut backend = UfliaDpllBackend;
    check_qf_abv_lazy_row(&mut backend, arena, assertions, config)
}

/// Sound UNSAT refuter for the Stump-Barrett-Dill-Levitt store disjunction:
///
/// ```text
/// store(a, i, v) = b ∧ store(a, j, w) = b  ⇒  i = j ∨ a = b
/// ```
///
/// If the existing congruence checker refutes both branches (`i = j` and
/// `a = b`) under the original assertions, the original array query is UNSAT.
/// This is intentionally a refuter only; if either branch is not refuted by
/// congruence, it declines without changing the query.
pub fn prove_unsat_by_two_store_same_target_split_within(
    arena: &mut TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Result<bool, SolverError> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        if past_deadline(deadline) {
            return Ok(false);
        }
        collect_positive_conjuncts(arena, assertion, &mut conjuncts);
    }

    let stores: Vec<StoreEquality> = conjuncts
        .into_iter()
        .filter_map(|term| store_equality(arena, term))
        .collect();

    for a in 0..stores.len() {
        if past_deadline(deadline) {
            return Ok(false);
        }
        for b in (a + 1)..stores.len() {
            if past_deadline(deadline) {
                return Ok(false);
            }
            let lhs = stores[a];
            let rhs = stores[b];
            if lhs.base != rhs.base || lhs.target != rhs.target {
                continue;
            }

            let same_index = arena
                .eq(lhs.index, rhs.index)
                .map_err(|e| SolverError::Backend(format!("array split index eq failed: {e}")))?;
            let same_array = arena
                .eq(lhs.base, lhs.target)
                .map_err(|e| SolverError::Backend(format!("array split base eq failed: {e}")))?;

            if congruence_refutes_with(arena, assertions, same_index)
                && congruence_refutes_with(arena, assertions, same_array)
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

/// Sound UNSAT refuter for generated swap-chain equalities. A term of the form
///
/// ```text
/// store(store(a, i, select(a, j)), j, select(a, i))
/// ```
///
/// swaps the values at `i` and `j`, and is extensionally equal to the same swap
/// written with `i`/`j` reversed. Therefore two array terms with the same base and
/// the same ordered sequence of unordered swap pairs are equal; any assertion
/// demanding different reads at the same index is UNSAT.
#[cfg(test)]
pub fn prove_unsat_by_symmetric_swap_chain(arena: &TermArena, assertions: &[TermId]) -> bool {
    prove_unsat_by_symmetric_swap_chain_within(arena, assertions, None)
}

pub fn prove_unsat_by_symmetric_swap_chain_within(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> bool {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        if past_deadline(deadline) {
            return false;
        }
        collect_positive_conjuncts(arena, assertion, &mut conjuncts);
    }

    let mut normalizer = SwapNormalizer::new(arena, deadline);
    for conjunct in conjuncts {
        if past_deadline(deadline) {
            return false;
        }
        let Some((lhs_array, rhs_array, lhs_index, rhs_index)) =
            negated_select_equality(arena, conjunct)
        else {
            continue;
        };
        if lhs_index != rhs_index {
            continue;
        }
        let lhs = normalizer.normalize(lhs_array);
        if normalizer.timed_out {
            return false;
        }
        let rhs = normalizer.normalize(rhs_array);
        if normalizer.timed_out {
            return false;
        }
        if lhs == rhs {
            return true;
        }
    }

    false
}

#[derive(Clone, Copy)]
struct StoreEquality {
    base: TermId,
    index: TermId,
    target: TermId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SwapChain {
    base: TermId,
    /// Mapping from an index in the final array to the index read from the base
    /// array. Missing entries are identity. A swap exchanges the mapped values
    /// at its two indices.
    image: BTreeMap<TermId, TermId>,
}

impl SwapChain {
    fn identity(base: TermId) -> Self {
        Self {
            base,
            image: BTreeMap::new(),
        }
    }

    fn apply_swap(&mut self, i: TermId, j: TermId) {
        if i == j {
            return;
        }
        let vi = self.image.get(&i).copied().unwrap_or(i);
        let vj = self.image.get(&j).copied().unwrap_or(j);
        set_permutation_image(&mut self.image, i, vj);
        set_permutation_image(&mut self.image, j, vi);
    }
}

fn set_permutation_image(image: &mut BTreeMap<TermId, TermId>, index: TermId, value: TermId) {
    if index == value {
        image.remove(&index);
    } else {
        image.insert(index, value);
    }
}

struct SwapNormalizer<'a> {
    arena: &'a TermArena,
    memo: HashMap<TermId, SwapChain>,
    deadline: Option<Instant>,
    timed_out: bool,
}

impl<'a> SwapNormalizer<'a> {
    fn new(arena: &'a TermArena, deadline: Option<Instant>) -> Self {
        Self {
            arena,
            memo: HashMap::new(),
            deadline,
            timed_out: false,
        }
    }

    fn normalize(&mut self, term: TermId) -> SwapChain {
        if self.past_deadline() {
            self.timed_out = true;
            return SwapChain::identity(term);
        }
        if let Some(chain) = self.memo.get(&term) {
            return chain.clone();
        }

        let chain = self
            .normalize_swap(term)
            .or_else(|| self.normalize_noop_store(term))
            .unwrap_or_else(|| SwapChain::identity(term));
        self.memo.insert(term, chain.clone());
        chain
    }

    fn past_deadline(&self) -> bool {
        past_deadline(self.deadline)
    }

    fn normalize_swap(&mut self, term: TermId) -> Option<SwapChain> {
        if self.past_deadline() {
            self.timed_out = true;
            return None;
        }
        let (base, i, j, inner_elem_base, outer_elem_base) = swap_parts(self.arena, term)?;
        let mut base_chain = self.normalize(base);
        if self.timed_out {
            return None;
        }
        let inner_chain = self.normalize(inner_elem_base);
        if self.timed_out {
            return None;
        }
        let outer_chain = self.normalize(outer_elem_base);
        if self.timed_out {
            return None;
        }
        if inner_chain == base_chain && outer_chain == base_chain {
            base_chain.apply_swap(i, j);
            Some(base_chain)
        } else {
            None
        }
    }

    fn normalize_noop_store(&mut self, term: TermId) -> Option<SwapChain> {
        if self.past_deadline() {
            self.timed_out = true;
            return None;
        }
        let (base, store_index, elem_base, elem_index) = noop_store_parts(self.arena, term)?;
        if store_index != elem_index {
            return None;
        }
        let base_chain = self.normalize(base);
        if self.timed_out {
            return None;
        }
        let elem_chain = self.normalize(elem_base);
        if self.timed_out {
            return None;
        }
        if elem_chain == base_chain {
            Some(base_chain)
        } else {
            None
        }
    }
}

fn negated_select_equality(
    arena: &TermArena,
    term: TermId,
) -> Option<(TermId, TermId, TermId, TermId)> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let eq = args[0];
    let TermNode::App {
        op: Op::Eq,
        args: eq_args,
    } = arena.node(eq)
    else {
        return None;
    };
    let (lhs_array, lhs_index) = select_parts(arena, eq_args[0])?;
    let (rhs_array, rhs_index) = select_parts(arena, eq_args[1])?;
    Some((lhs_array, rhs_array, lhs_index, rhs_index))
}

fn select_parts(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::Select,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    Some((args[0], args[1]))
}

fn swap_parts(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, TermId, TermId, TermId)> {
    let TermNode::App {
        op: Op::Store,
        args: outer,
    } = arena.node(term)
    else {
        return None;
    };
    let inner_store = outer[0];
    let outer_index = outer[1];
    let outer_elem = outer[2];
    let TermNode::App {
        op: Op::Store,
        args: inner,
    } = arena.node(inner_store)
    else {
        return None;
    };
    let base = inner[0];
    let inner_index = inner[1];
    let inner_elem = inner[2];
    let (inner_elem_base, inner_elem_index) = select_parts(arena, inner_elem)?;
    let (outer_elem_base, outer_elem_index) = select_parts(arena, outer_elem)?;
    if inner_elem_index == outer_index && outer_elem_index == inner_index {
        Some((
            base,
            inner_index,
            outer_index,
            inner_elem_base,
            outer_elem_base,
        ))
    } else {
        None
    }
}

fn noop_store_parts(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, TermId, TermId)> {
    let TermNode::App {
        op: Op::Store,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let base = args[0];
    let store_index = args[1];
    let (elem_base, elem_index) = select_parts(arena, args[2])?;
    Some((base, store_index, elem_base, elem_index))
}

fn collect_positive_conjuncts(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } => {
            for &arg in args {
                collect_positive_conjuncts(arena, arg, out);
            }
        }
        _ => out.push(term),
    }
}

fn store_equality(arena: &TermArena, term: TermId) -> Option<StoreEquality> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let (lhs, rhs) = (args[0], args[1]);
    store_side(arena, lhs, rhs).or_else(|| store_side(arena, rhs, lhs))
}

fn store_side(arena: &TermArena, store: TermId, target: TermId) -> Option<StoreEquality> {
    let TermNode::App {
        op: Op::Store,
        args,
    } = arena.node(store)
    else {
        return None;
    };
    if !matches!(arena.sort_of(store), Sort::Array { .. })
        || arena.sort_of(target) != arena.sort_of(store)
    {
        return None;
    }
    Some(StoreEquality {
        base: args[0],
        index: args[1],
        target,
    })
}

fn congruence_refutes_with(arena: &TermArena, assertions: &[TermId], extra: TermId) -> bool {
    let mut branch = Vec::with_capacity(assertions.len() + 1);
    branch.extend_from_slice(assertions);
    branch.push(extra);
    crate::euf_egraph::prove_unsat_by_congruence(arena, &branch).is_some()
}

struct ArithDpllBackend;

impl SolverBackend for ArithDpllBackend {
    fn capabilities(&self) -> Capabilities {
        Capabilities {
            name: "arith-dpll".to_owned(),
            produces_models: true,
            complete: true,
        }
    }

    fn check(
        &mut self,
        arena: &TermArena,
        assertions: &[TermId],
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        let mut scratch = arena.clone();
        crate::dpll_lia::check_with_arith_dpll(&mut scratch, assertions, config)
    }
}

struct UfliaDpllBackend;

impl SolverBackend for UfliaDpllBackend {
    fn capabilities(&self) -> Capabilities {
        Capabilities {
            name: "uflia-dpll".to_owned(),
            produces_models: true,
            complete: true,
        }
    }

    fn check(
        &mut self,
        arena: &TermArena,
        assertions: &[TermId],
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        let mut scratch = arena.clone();
        match crate::uflia_online::check_qf_uflia_online(&mut scratch, assertions, config)? {
            CheckResult::Unknown(reason) if !is_budget_unknown_kind(reason.kind) => {
                let mut eager = arena.clone();
                crate::check_with_uf_arithmetic(&mut eager, assertions, config)
            }
            result => Ok(result),
        }
    }
}

fn is_budget_unknown_kind(kind: UnknownKind) -> bool {
    matches!(
        kind,
        UnknownKind::Timeout
            | UnknownKind::ResourceLimit
            | UnknownKind::MemoryLimit
            | UnknownKind::NodeBudget
            | UnknownKind::EncodingBudget
    )
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
    /// The fresh scalar variable that abstracts this read's result.
    fresh: SymbolId,
    /// The (already-rewritten) index term.
    index: TermId,
    /// How the read resolves: a store (ROW), a variable, or a constant array.
    kind: RowKind,
}

/// How an abstracted read resolves under the read-over-write axiom.
#[derive(Clone)]
enum RowKind {
    /// `select(store(_, store_index, store_elem), index)`; `inner` is the
    /// already-abstracted scalar expression for `select(base', index)`.
    Store {
        store_index: TermId,
        store_elem: TermId,
        inner: TermId,
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
    /// `(base term, index term) -> abstracted scalar read expression`.
    memo: HashMap<(TermId, TermId), TermId>,
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
                let Some(read) = self.resolve_select(arena, args[0], index)? else {
                    return Ok(None);
                };
                Ok(Some(read))
            }
            TermNode::App { op: Op::Store, .. } => {
                // A bare store in a non-select position cannot be abstracted to a
                // scalar; decline.
                Ok(None)
            }
            TermNode::App {
                op: op @ Op::Apply(_),
                args,
            } => {
                let mut new_args = Vec::with_capacity(args.len());
                for arg in args {
                    if matches!(arena.sort_of(arg), Sort::Array { .. }) {
                        new_args.push(arg);
                    } else {
                        let Some(t) = self.abstract_term(arena, arg)? else {
                            return Ok(None);
                        };
                        new_args.push(t);
                    }
                }
                Ok(Some(rebuild_app(arena, op, &new_args)?))
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

    /// Materialises (or reuses) the abstract scalar expression for
    /// `select(base, index)` with `index` already abstracted. Store/variable/const
    /// reads allocate fresh sites; array-valued `ite` reads lower to scalar `ite`
    /// over the recursively resolved branch reads. `None` declines an unmodellable
    /// base shape.
    fn resolve_select(
        &mut self,
        arena: &mut TermArena,
        base: TermId,
        index: TermId,
    ) -> Result<Option<TermId>, SolverError> {
        if let Some(&read) = self.memo.get(&(base, index)) {
            return Ok(Some(read));
        }
        let Some((_index_sort, element_sort)) = arena.sort_of(base).array_sorts() else {
            return Ok(None);
        };
        let node = arena.node(base).clone();
        let read = match node {
            TermNode::App {
                op: Op::Store,
                args,
            } => {
                if self.sites.len() >= MAX_ROW_SITES {
                    return Ok(None);
                }
                let Some(store_index) = self.abstract_term(arena, args[1])? else {
                    return Ok(None);
                };
                let Some(store_elem) = self.abstract_term(arena, args[2])? else {
                    return Ok(None);
                };
                let Some(inner) = self.resolve_select(arena, args[0], index)? else {
                    return Ok(None);
                };
                let kind = RowKind::Store {
                    store_index,
                    store_elem,
                    inner,
                };
                let fresh = self.fresh_symbol(arena, element_sort)?;
                self.sites.push(RowSite { fresh, index, kind });
                arena.var(fresh)
            }
            TermNode::App { op: Op::Ite, args } => {
                let Some(condition) = self.abstract_term(arena, args[0])? else {
                    return Ok(None);
                };
                let Some(then_read) = self.resolve_select(arena, args[1], index)? else {
                    return Ok(None);
                };
                let Some(else_read) = self.resolve_select(arena, args[2], index)? else {
                    return Ok(None);
                };
                arena
                    .ite(condition, then_read, else_read)
                    .map_err(|e| SolverError::Backend(format!("lazy-ROW ite read failed: {e}")))?
            }
            TermNode::Symbol(sym) if matches!(arena.sort_of(base), Sort::Array { .. }) => {
                if self.sites.len() >= MAX_ROW_SITES {
                    return Ok(None);
                }
                let kind = RowKind::Var { array: sym };
                let fresh = self.fresh_symbol(arena, element_sort)?;
                self.sites.push(RowSite { fresh, index, kind });
                arena.var(fresh)
            }
            TermNode::App {
                op: Op::ConstArray { .. },
                args,
            } => {
                if self.sites.len() >= MAX_ROW_SITES {
                    return Ok(None);
                }
                let Some(value) = self.abstract_term(arena, args[0])? else {
                    return Ok(None);
                };
                let kind = RowKind::Const { value };
                let fresh = self.fresh_symbol(arena, element_sort)?;
                self.sites.push(RowSite { fresh, index, kind });
                arena.var(fresh)
            }
            // Other array-valued structural bases remain outside this fragment.
            _ => return Ok(None),
        };
        self.memo.insert((base, index), read);
        Ok(Some(read))
    }

    fn fresh_symbol(&mut self, arena: &mut TermArena, sort: Sort) -> Result<SymbolId, SolverError> {
        let name = format!("!row_sel_{}", self.fresh_counter);
        self.fresh_counter += 1;
        arena
            .declare(&name, sort)
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
            TermNode::App {
                op: op @ Op::Apply(_),
                args,
            } => {
                let mut new_args = Vec::with_capacity(args.len());
                for arg in args {
                    if matches!(arena.sort_of(arg), Sort::Array { .. }) {
                        new_args.push(arg);
                    } else {
                        let Some(t) = self.abstract_with_array_eq(arena, arg)? else {
                            return Ok(None);
                        };
                        new_args.push(t);
                    }
                }
                Ok(Some(rebuild_app(arena, op, &new_args)?))
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

/// Solves one scalar abstraction snapshot after model-sound word-level
/// preprocessing.
///
/// The ROW/extensionality abstractions generate many top-level definitions
/// (`fresh_read = select(...)`, scalar aliases, branch guards). Running the
/// existing preprocessing wrapper here removes those aliases before the scalar
/// backend sees the Boolean/theory skeleton. This is still a relaxation-side
/// optimization only: `unsat` of the preprocessed snapshot implies `unsat` of the
/// snapshot, while `sat` is reconstructed by the wrapper and then subjected to
/// the normal ROW/extensionality projection and original-formula replay.
fn check_scalar_abstraction<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let mut flattened = Vec::new();
    for &assertion in assertions {
        collect_positive_conjuncts(arena, assertion, &mut flattened);
    }
    match crate::preprocess::check_with_preprocessing_and_local_search(
        backend,
        arena,
        &flattened,
        config,
        Duration::from_millis(SCALAR_LOCAL_SEARCH_PROBE_MS),
    ) {
        Ok(result) => Ok(result),
        Err(_) => backend.check(arena, &flattened, config),
    }
}

#[allow(clippy::too_many_lines)]
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

    for round in 0..MAX_ROW_ROUNDS {
        if past_deadline(deadline) {
            return Ok(row_unknown(
                "lazy-ROW deadline exceeded before refinement converged".to_owned(),
            ));
        }
        let round_config = config_with_remaining_deadline(config, deadline);
        let assignment = match check_scalar_abstraction(backend, arena, &working, &round_config)? {
            // The abstraction is a relaxation; its UNSAT implies the original's.
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(reason) => {
                return Ok(contextual_unknown(
                    "lazy-ROW scalar backend declined",
                    round,
                    ctx.sites.len(),
                    added_row.len(),
                    added_cong.len(),
                    &reason,
                ));
            }
            CheckResult::Sat(model) => complete_assignment(arena, &model.to_assignment()),
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
    let j = eval(arena, site.index, assignment).map_err(ir)?;
    let i = eval(arena, *store_index, assignment).map_err(ir)?;
    let Some(actual) = assignment.get(site.fresh) else {
        return Ok(false);
    };
    let expected = if i == j {
        eval(arena, *store_elem, assignment).map_err(ir)?
    } else {
        eval(arena, *inner, assignment).map_err(ir)?
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
    let same_index = arena.eq(site.index, store_index).map_err(ir)?;
    let r_eq_elem = arena.eq(r, store_elem).map_err(ir)?;
    let r_eq_inner = arena.eq(r, inner).map_err(ir)?;
    let hit = arena.implies(same_index, r_eq_elem).map_err(ir)?;
    let not_same = arena.not(same_index).map_err(ir)?;
    let miss = arena.implies(not_same, r_eq_inner).map_err(ir)?;
    arena.and(hit, miss).map_err(ir)
}

/// Model-completes every declared symbol with the IR's well-founded default.
///
/// Some scalar backends only bind symbols that appear in their abstraction. Array
/// replay still needs values for original index symbols that may have disappeared
/// from the scalar formula, so complete before evaluating projection metadata.
fn complete_assignment(arena: &TermArena, assignment: &Assignment) -> Assignment {
    let mut out = assignment.clone();
    for (symbol, _name, sort) in arena.symbols() {
        if out.get(symbol).is_none() {
            if let Some(value) = well_founded_default(arena, sort) {
                out.set(symbol, value);
            }
        }
    }
    for (func, _name, params, result) in arena.functions() {
        if out.function(func).is_none()
            && let Some(value) = default_func_value(arena, params, result)
        {
            out.set_function(func, value);
        }
    }
    out
}

fn default_func_value(arena: &TermArena, params: &[Sort], result: Sort) -> Option<FuncValue> {
    if FuncValue::uses_value_storage_for(params, result) {
        let default = well_founded_default(arena, result)?;
        Some(FuncValue::constant_value(params.to_vec(), result, default))
    } else {
        Some(FuncValue::constant(params.to_vec(), result, 0))
    }
}

/// Collects base-array read-site entries `(index value, selected value)` in
/// deterministic site discovery order, grouped by array symbol.
fn collect_base_array_entries(
    arena: &TermArena,
    ctx: &RowCtx,
    assignment: &Assignment,
    context: &str,
) -> Result<BTreeMap<SymbolId, Vec<(Value, Value)>>, SolverError> {
    let ir = |e: axeyum_ir::IrError| SolverError::Backend(format!("{context}: {e}"));
    let mut arrays: BTreeMap<SymbolId, Vec<(Value, Value)>> = BTreeMap::new();
    for site in &ctx.sites {
        if let RowKind::Var { array } = site.kind {
            let index = eval(arena, site.index, assignment).map_err(ir)?;
            let Some(value) = assignment.get(site.fresh) else {
                continue;
            };
            arrays.entry(array).or_default().push((index, value));
        }
    }
    Ok(arrays)
}

/// Builds a concrete array value for `array` from projected read entries.
fn array_value_from_entries(
    arena: &TermArena,
    array: SymbolId,
    entries: &[(Value, Value)],
) -> Result<Value, SolverError> {
    let sort = arena.symbol(array).1;
    if let Some((index_width, element_width)) = sort.array_widths() {
        let mut value = ArrayValue::constant(index_width, element_width, 0);
        for (index, element) in entries {
            let (_, index) = index.as_bv().ok_or_else(|| {
                SolverError::Backend("array projection expected a bit-vector index".to_owned())
            })?;
            let (_, element) = element.as_bv().ok_or_else(|| {
                SolverError::Backend("array projection expected a bit-vector element".to_owned())
            })?;
            value = value.store(index, element);
        }
        return Ok(Value::Array(value));
    }

    let Sort::Array { index, element } = sort else {
        return Err(SolverError::Backend(
            "array projection requested for a non-array symbol".to_owned(),
        ));
    };
    let default = well_founded_default(arena, element.to_sort()).ok_or_else(|| {
        SolverError::Backend(
            "array projection could not construct a default element value".to_owned(),
        )
    })?;
    let mut value = GenericArrayValue::constant(index, element, default);
    for (entry_index, entry_element) in entries {
        value = value.store(entry_index.clone(), entry_element.clone());
    }
    Ok(Value::GenericArray(value))
}

fn is_array_value(value: &Value) -> bool {
    matches!(value, Value::Array(_) | Value::GenericArray(_))
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
    // Reconstruct array variables from the base-variable read sites only (store
    // reads resolve through the ROW axiom, not a stored array variable).
    let arrays = collect_base_array_entries(arena, ctx, assignment, "lazy-ROW projection failed")?;
    let mut projected = complete_assignment(arena, assignment);
    for (&array, entries) in &arrays {
        projected.set(array, array_value_from_entries(arena, array, entries)?);
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
            if let Ok(value) = eval(arena, body, &projected) {
                if is_array_value(&value) && projected.get(sym).as_ref() != Some(&value) {
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
    for (func, value) in projected.functions() {
        out.set_function(func, value.clone());
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

    for round in 0..MAX_ROW_ROUNDS {
        if past_deadline(deadline) {
            return Ok(ext_unknown(
                "lazy-extensionality deadline exceeded before refinement converged".to_owned(),
            ));
        }
        let round_config = config_with_remaining_deadline(config, deadline);
        let assignment = match check_scalar_abstraction(backend, arena, &working, &round_config)? {
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(reason) => {
                return Ok(contextual_unknown(
                    "lazy-extensionality scalar backend declined",
                    round,
                    ctx.sites.len(),
                    added_row.len(),
                    added_cong.len(),
                    &reason,
                ));
            }
            CheckResult::Sat(model) => complete_assignment(arena, &model.to_assignment()),
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
        let Some(read_a) = ctx.resolve_select(arena, lhs, index)? else {
            continue;
        };
        let Some(read_b) = ctx.resolve_select(arena, rhs, index)? else {
            continue;
        };
        // `resolve_select` can materialize a fresh read symbol after the scalar
        // assignment was completed. Complete again before evaluating the read
        // terms so an unassigned fresh does not turn a candidate into a backend
        // error; the eventual projected model is still replay-gated.
        let completed = complete_assignment(arena, assignment);
        if read_terms_differ(arena, read_a, read_b, &completed)? {
            let var_flag = arena.var(flag);
            let eqr = arena
                .eq(read_a, read_b)
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
    let Some((index_sort, _)) = arena.sort_of(lhs).array_sorts() else {
        return Ok(());
    };
    let name = format!("!ext_diff_{}", ctx.fresh_counter);
    ctx.fresh_counter += 1;
    let k_sym = arena
        .declare(&name, index_sort)
        .map_err(|e| SolverError::Backend(format!("lazy-ext diff-skolem declare failed: {e}")))?;
    let k = arena.var(k_sym);

    let Some(read_a) = ctx.resolve_select(arena, lhs, k)? else {
        return Ok(());
    };
    let Some(read_b) = ctx.resolve_select(arena, rhs, k)? else {
        return Ok(());
    };
    let var_flag = arena.var(flag);
    let not_flag = arena
        .not(var_flag)
        .map_err(|e| SolverError::Backend(format!("lazy-ext diff build failed: {e}")))?;
    let eqr = arena
        .eq(read_a, read_b)
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
    // Reconstruct array variables from the base-variable read sites only.
    let arrays = collect_base_array_entries(arena, ctx, assignment, "lazy-ext projection failed")?;
    let mut projected = complete_assignment(arena, assignment);
    for (&array, entries) in &arrays {
        projected.set(array, array_value_from_entries(arena, array, entries)?);
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
    for (func, value) in projected.functions() {
        out.set_function(func, value.clone());
    }
    Ok(CheckResult::Sat(out))
}

// ===========================================================================
// Eager array-elimination UNSAT CERTIFICATE (narrows the `TrustId::ArrayElim`
// hole for the eager-elimination UNSAT sub-case).
// ===========================================================================
//
// [`check_with_array_elimination`] reaches a TRUSTED `Unsat` for a `QF_ABV`
// query: it eagerly eliminates arrays ([`eliminate_arrays`], ADR-0010) to a pure
// `QF_BV` formula and refutes that. The `QF_BV` layer already carries DRAT
// (`export_qf_bv_unsat_proof` → `check_drat`), but the ABV→BV *reduction* — that
// the eliminated formula is a SOUND relaxation of the original array formula — is
// the `ArrayElim` trust hole. This certificate makes that reduction
// independently re-checkable for the eager-elimination UNSAT sub-case, mirroring
// the bounded int-blast certificate (commit 6211982) and COMPOSING the Ackermann
// select-congruence witness (commit d7394ec) — array elim's second step IS an
// Ackermann congruence reduction (over a per-array read function with a single
// index argument).
//
// SOUNDNESS DIRECTION (why `QF_BV`-UNSAT ⇒ ABV-UNSAT). `eliminate_arrays` does
// two things, each a SOUND step:
//
//   1. **Read-over-write.** It rewrites `select(store(a,i,e),j)` to
//      `ite(i=j, e, select(a,j))` and `select(ite(c,t,e),j)` to
//      `ite(c, select(t,j), select(e,j))` until every remaining `select` reads an
//      array *variable*. Each rewrite is a VALID array-theory EQUIVALENCE (the LHS
//      and RHS denote the same element in every array model), so the rewritten
//      formula is equisatisfiable with the original — no models are gained or lost.
//      The result is the `abstraction`: every `select(a, idx)` over an array
//      variable replaced by a fresh `BitVec` variable `v_{a,idx}` (consistently
//      interned: identical `(a, idx)` reads share one fresh var).
//   2. **Ackermann select-congruence.** For every pair of selects on the SAME
//      array variable it appends the constraint `(idx_i = idx_j) ⇒ (v_i = v_j)`.
//      Each such constraint is a VALID consequence of `a` being a function of its
//      index (equal indices read equal elements). Therefore EVERY model `M` of the
//      original array formula extends to a model of the eliminated `QF_BV` formula
//      (interpret each `v_{a,idx}` as `a^M[idx^M]`; the rewritten body holds
//      because read-over-write is an equivalence, and every congruence constraint
//      holds because `a^M` is a genuine function). So the eliminated formula is a
//      sound over-approximation (relaxation): if it is UNSAT, the original has no
//      model either. As with the UF Ackermann case, for the UNSAT direction even a
//      *subset* of the congruence constraints would remain sound (fewer
//      constraints only enlarge the model set) — the witness merely confirms each
//      appended constraint is a real, valid congruence, never a spurious extra
//      assertion that could make a satisfiable formula look UNSAT.
//
// The certificate's `recheck` re-runs the deterministic elimination on the
// ORIGINAL assertions, structurally re-derives the select-congruence set from the
// discovered read pairs and confirms the eliminated formula is exactly
// `abstraction ++ pairwise-congruence` (so it IS a sound relaxation, witnessed —
// not asserted), re-bit-blasts that eliminated formula and confirms the stored
// DIMACS is byte-identical (the DRAT refutes precisely THIS CNF), and re-runs
// `check_drat` over the stored DIMACS/DRAT. Trusting nothing the emitter computed.

/// Deterministic admission bound on the number of eager select-congruence pairs a
/// certificate will witness, mirroring the UF eager bound in [`crate::euf`]. Above
/// this, [`certify_array_elim_unsat`] declines (no certificate) rather than build
/// and re-derive the `O(k²)` pairing.
const MAX_ARRAY_ELIM_CONGRUENCE_PAIRS: usize = 256;

/// A re-checkable certificate that a `QF_ABV` query is `Unsat` via **eager array
/// elimination** (read-over-write + Ackermann select-congruence, ADR-0010): the
/// bit-blasted-CNF DRAT refutation of the (deterministically) array-eliminated
/// formula, plus the witnessed shape of the elimination (the per-array
/// select-congruence-pair counts) so the reduction can be re-derived and confirmed.
/// See [`ArrayElimUnsatCertificate::recheck`].
#[derive(Debug, Clone)]
pub struct ArrayElimUnsatCertificate {
    /// Per-array select-congruence-pair counts `(array, pairs)` in discovery order:
    /// `pairs = k·(k−1)/2` for an array variable read at `k` distinct sites. Purely
    /// descriptive (re-derived and confirmed by `recheck`); records the witnessed
    /// shape of the eager select-congruence (Ackermann) expansion.
    congruence_pairs_per_array: Vec<(SymbolId, usize)>,
    /// Total appended select-congruence constraints (`Σ pairs`): the size of the
    /// valid-consequence set the eliminated formula adds over the rewritten
    /// (read-over-write) abstraction. Re-derived and confirmed by `recheck`.
    congruence_constraint_count: usize,
    /// DRAT (+ DIMACS) refutation of the bit-blasted, array-eliminated `QF_BV` CNF,
    /// independently re-checkable by `check_drat`.
    bv_proof: crate::proof::UnsatProof,
}

impl ArrayElimUnsatCertificate {
    /// The per-array select-congruence-pair counts `(array, pairs)`, in discovery
    /// order.
    #[must_use]
    pub fn congruence_pairs_per_array(&self) -> &[(SymbolId, usize)] {
        &self.congruence_pairs_per_array
    }

    /// The total number of appended select-congruence constraints.
    #[must_use]
    pub fn congruence_constraint_count(&self) -> usize {
        self.congruence_constraint_count
    }

    /// The bit-blasted-CNF DRAT certificate of the array-eliminated formula.
    #[must_use]
    pub fn bv_proof(&self) -> &crate::proof::UnsatProof {
        &self.bv_proof
    }

    /// **Independently re-validates** the whole eager array-elimination reduction
    /// plus the BV refutation, from the ORIGINAL `assertions` and this
    /// certificate's stored data, trusting nothing the emitter computed:
    ///
    ///  1. re-runs the deterministic [`eliminate_arrays`] on `assertions`;
    ///  2. structurally re-derives the pairwise select-congruence set from the
    ///     discovered read sites and confirms the eliminated formula is *exactly*
    ///     `abstraction (read-over-write) ++ that-congruence-set` (so each appended
    ///     assertion is a VALID select-congruence consequence — the eliminated
    ///     formula is a sound relaxation, witnessed) and that the recorded pair
    ///     counts match;
    ///  3. re-bit-blasts the re-derived eliminated formula and confirms the stored
    ///     DIMACS is byte-identical (the DRAT refutes precisely *this* CNF);
    ///  4. re-runs `check_drat` (RUP/RAT) over the stored DIMACS/DRAT.
    ///
    /// Returns `Ok(true)` only when all four hold. With the reduction re-derived
    /// (2,3) and the refutation re-checked (4), `QF_BV`-UNSAT ⇒ ABV-UNSAT, so this
    /// `Unsat` carries no residual `ArrayElim` trust for this eager sub-case. A
    /// `false`/`Err` means the certificate does not establish the `Unsat` and must
    /// not be trusted.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if the elimination/bit-blast fails or the stored
    /// DRAT/DIMACS is unparseable.
    pub fn recheck(&self, arena: &TermArena, assertions: &[TermId]) -> Result<bool, SolverError> {
        // (1) Re-run the deterministic elimination on a scratch copy of the
        //     ORIGINAL assertions. Trust nothing stored: the eliminated formula and
        //     its blast are recomputed here.
        let mut scratch = arena.clone();
        let Ok(elim) = eliminate_arrays(&mut scratch, assertions) else {
            return Ok(false);
        };
        if !elim.had_arrays() {
            // No array constructs: nothing was array-eliminated, so there is no
            // eager array-elim reduction for this certificate to stand for.
            return Ok(false);
        }

        // (2) Structurally re-derive the pairwise select-congruence set and confirm
        //     the eliminated formula is exactly `abstraction ++ congruence`.
        let Some((rederived, per_array)) = rederive_select_congruence(&mut scratch, &elim) else {
            return Ok(false);
        };
        let abstraction = elim.abstraction();
        let eliminated = elim.assertions();
        if eliminated.len() != abstraction.len() + rederived.len() {
            return Ok(false);
        }
        if eliminated[..abstraction.len()] != *abstraction {
            return Ok(false);
        }
        if eliminated[abstraction.len()..] != rederived[..] {
            return Ok(false);
        }
        if per_array != self.congruence_pairs_per_array
            || rederived.len() != self.congruence_constraint_count
        {
            return Ok(false);
        }

        // (3) Re-bit-blast the re-derived eliminated formula and confirm the stored
        //     DIMACS is byte-identical: the DRAT refutes precisely the CNF of the
        //     formula we just re-derived, not some unrelated CNF the emitter chose.
        let eliminated = eliminated.to_vec();
        match crate::proof::export_qf_bv_unsat_proof(&scratch, &eliminated)? {
            crate::proof::UnsatProofOutcome::Proved(fresh) => {
                if fresh.dimacs != self.bv_proof.dimacs {
                    return Ok(false);
                }
            }
            // The re-derived eliminated formula is SAT or undecided: the stored
            // UNSAT certificate cannot stand.
            crate::proof::UnsatProofOutcome::Satisfiable
            | crate::proof::UnsatProofOutcome::Inconclusive => return Ok(false),
        }

        // (4) Independently re-check the stored BV refutation (RUP/RAT) over the
        //     stored DIMACS/DRAT.
        self.bv_proof.recheck()
    }
}

/// The re-derived select-congruence set: the constraint terms (in eliminator-append
/// order) paired with the per-array congruence-pair counts `(array, pairs)`.
type RederivedSelectCongruence = (Vec<TermId>, Vec<(SymbolId, usize)>);

/// Structurally re-derives the eager Ackermann select-congruence constraints from
/// an elimination's discovered selects, replicating exactly what
/// [`eliminate_arrays`] appends: per array variable (discovery order), for every
/// `i < j` read pair, `(idx_i = idx_j) ⇒ (v_i = v_j)`. Returns the constraint
/// terms (in the same order the eliminator appends them) and the per-array pair
/// counts. `None` on an IR builder failure.
///
/// Because these terms are rebuilt on the SAME (post-elimination) `arena` whose
/// interning gives identity, the returned `TermId`s are directly comparable to the
/// eliminated formula's appended constraints — so a match *witnesses* that every
/// appended assertion is a genuine, valid select-congruence consequence. The build
/// (`implies(eq(idx_i, idx_j), eq(v_i, v_j))`, in array-then-pair order) mirrors
/// `Eliminator::ackermann_constraints` verbatim.
fn rederive_select_congruence(
    arena: &mut TermArena,
    elim: &ArrayElimination,
) -> Option<RederivedSelectCongruence> {
    // Snapshot the eliminated selects `(array, index, fresh)` in discovery order.
    let selects: Vec<(SymbolId, TermId, SymbolId)> = elim.selects();

    // Group select indices by array symbol, preserving discovery order — the same
    // grouping order `Eliminator::record_select` uses (linear find, no hash-map
    // iteration in any output).
    let mut groups: Vec<(SymbolId, Vec<usize>)> = Vec::new();
    for (idx, (array, _index, _fresh)) in selects.iter().enumerate() {
        if let Some((_, members)) = groups.iter_mut().find(|(a, _)| a == array) {
            members.push(idx);
        } else {
            groups.push((*array, vec![idx]));
        }
    }

    let mut constraints = Vec::new();
    let mut per_array = Vec::new();
    for (array, members) in &groups {
        let mut pairs = 0usize;
        for a in 0..members.len() {
            for b in (a + 1)..members.len() {
                let (_ai, index_i, fresh_i) = selects[members[a]];
                let (_aj, index_j, fresh_j) = selects[members[b]];
                // Same construction as `select_congruence_lemma` /
                // `Eliminator::ackermann_constraints`: `(idx_i = idx_j) ⇒ (v_i = v_j)`.
                let constraint =
                    select_congruence_lemma(arena, index_i, index_j, fresh_i, fresh_j).ok()?;
                constraints.push(constraint);
                pairs += 1;
            }
        }
        per_array.push((*array, pairs));
    }
    Some((constraints, per_array))
}

/// Counts the total eager select-congruence pairs `eliminate_arrays` would append
/// for `assertions` (`Σ_a k_a·(k_a−1)/2` over array variables read at `k_a`
/// distinct sites), without building them. Used as the deterministic admission
/// bound. `None` if elimination refuses (out of the supported array fragment).
fn array_elim_congruence_pairs(arena: &TermArena, assertions: &[TermId]) -> Option<usize> {
    let mut scratch = arena.clone();
    let elim = eliminate_arrays(&mut scratch, assertions).ok()?;
    let selects = elim.selects();
    let mut groups: Vec<(SymbolId, usize)> = Vec::new();
    for (array, _index, _fresh) in &selects {
        if let Some((_, count)) = groups.iter_mut().find(|(a, _)| a == array) {
            *count += 1;
        } else {
            groups.push((*array, 1));
        }
    }
    Some(
        groups
            .iter()
            .map(|(_, k)| k * k.saturating_sub(1) / 2)
            .sum(),
    )
}

/// Attempts to produce a fully re-checkable [`ArrayElimUnsatCertificate`] for a
/// `QF_ABV` `assertions`: eagerly eliminates arrays ([`eliminate_arrays`] —
/// read-over-write + Ackermann select-congruence), bit-blasts the eliminated
/// `QF_BV` formula, and — if that CNF is `Unsat` — emits the DRAT bundled with the
/// witnessed shape of the elimination.
///
/// Returns `Ok(None)` when there are no array constructs to eliminate (not the
/// eager array-elim fragment), the instance is over the deterministic admission
/// bound (`MAX_ARRAY_ELIM_CONGRUENCE_PAIRS` — graceful, no `O(k²)` blowup), the
/// query is outside the supported array fragment, the eliminated formula is `Sat`,
/// or the proof core stays inconclusive. The verdict path is unchanged; this only
/// adds a certificate when one cleanly exists.
///
/// This is the **certifying** entry point for eager array-elimination `QF_ABV`
/// `Unsat`: a returned certificate, re-checked by
/// [`ArrayElimUnsatCertificate::recheck`] against the same `assertions`,
/// establishes the `Unsat` with no residual `ArrayElim` trust for this
/// eager-elimination sub-case.
///
/// # Errors
///
/// Returns [`SolverError`] on an internal elimination/encoding/blast failure.
pub fn certify_array_elim_unsat(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<ArrayElimUnsatCertificate>, SolverError> {
    // Deterministic admission bound: refuse the O(k²) eager congruence expansion
    // above the cap rather than build and re-derive it.
    match array_elim_congruence_pairs(arena, assertions) {
        Some(pairs) if pairs <= MAX_ARRAY_ELIM_CONGRUENCE_PAIRS => {}
        // Over the bound, or elimination refused (out-of-fragment): no certificate.
        _ => return Ok(None),
    }

    // Eliminate on a scratch arena (additive; the caller's arena is untouched).
    let mut scratch = arena.clone();
    let elim = eliminate_arrays(&mut scratch, assertions).map_err(map_elim_error)?;
    if !elim.had_arrays() {
        // No array constructs: there is no eager array-elim reduction to certify
        // here (pure QF_BV has its own exporter).
        return Ok(None);
    }

    // Witness the elimination's shape by structurally re-deriving the
    // select-congruence set; it must equal what `eliminate_arrays` appended.
    let Some((rederived, per_array)) = rederive_select_congruence(&mut scratch, &elim) else {
        return Ok(None);
    };
    let abstraction = elim.abstraction();
    let eliminated = elim.assertions();
    if eliminated.len() != abstraction.len() + rederived.len()
        || eliminated[..abstraction.len()] != *abstraction
        || eliminated[abstraction.len()..] != rederived[..]
    {
        return Ok(None);
    }
    let congruence_constraint_count = rederived.len();

    let eliminated = eliminated.to_vec();
    match crate::proof::export_qf_bv_unsat_proof(&scratch, &eliminated)? {
        crate::proof::UnsatProofOutcome::Proved(bv_proof) => Ok(Some(ArrayElimUnsatCertificate {
            congruence_pairs_per_array: per_array,
            congruence_constraint_count,
            bv_proof,
        })),
        crate::proof::UnsatProofOutcome::Satisfiable
        | crate::proof::UnsatProofOutcome::Inconclusive => Ok(None),
    }
}

#[cfg(test)]
#[allow(clippy::many_single_char_names, clippy::similar_names)]
mod tests {
    use super::{
        check_qf_abv_lazy, check_with_array_elimination, prove_unsat_by_symmetric_swap_chain,
    };
    use crate::backend::{CheckResult, SolverConfig};
    use crate::sat_bv_backend::SatBvBackend;
    use axeyum_ir::{TermArena, Value, eval};
    use axeyum_smtlib::parse_script;

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

    #[test]
    fn symmetric_swap_chain_refuter_closes_cvc5_regression() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__swap_t1_pp_nf_ai_00010_004.cvc.smt2"
        ))
        .unwrap();

        assert!(
            prove_unsat_by_symmetric_swap_chain(&script.arena, &script.assertions),
            "expected the structural swap-chain refuter to close the real cvc5 regression"
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
