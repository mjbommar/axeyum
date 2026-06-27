//! First-class `QF_ABV` solving by eager array elimination (ADR-0010).
//!
//! [`check_with_array_elimination`] is the consumer-facing entry point for
//! queries that use `select`/`store`: it eagerly eliminates arrays to `QF_BV`,
//! solves the result with any [`SolverBackend`], and on `sat` projects the
//! model back to array values and replays it against the original array
//! assertions with the ground evaluator. Pure `QF_BV` queries pass straight
//! through unchanged.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;
use std::time::{Duration, Instant};

use axeyum_ir::{
    ArraySortKey, ArrayValue, Assignment, FuncValue, GenericArrayValue, Op, Sort, SymbolId,
    TermArena, TermId, TermNode, Value, eval, well_founded_default,
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
///   which bounded extensionality declines above its small finite-index cap — does the
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

/// Decides the pure declared-sort `QF_AX` array slice through the same lazy
/// ROW/extensionality CEGAR used for BV and Int arrays, but with the replaying
/// EUF e-graph backend as the scalar solver.
///
/// This covers arrays indexed by and returning declared uninterpreted carriers:
/// every `select` is abstracted to a fresh carrier value, ROW/extensionality
/// lemmas are added on demand, and a final `sat` is projected to
/// [`GenericArrayValue`]s and replayed against the original assertions before it
/// is returned.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] when the input contains array or scalar
/// constructs outside this declared-sort array slice, and propagates scalar
/// backend errors from the replaying EUF solver.
pub fn check_qf_ax_declared_sort_lazy_row(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let mut backend = DeclaredSortEufBackend;
    check_qf_abv_lazy_row(&mut backend, arena, assertions, config)
}

/// A checked refutation for finite write chains over two different constant
/// arrays on an infinite (`Int`) index sort.
///
/// If `A = store(...((as const) d1)...)` and
/// `B = store(...((as const) d2)...)` with `d1 != d2`, then `A = B` is
/// impossible over `Int`: finitely many stores can affect only finitely many
/// indices, so some index outside both write sets still reads `d1` from `A` and
/// `d2` from `B`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstArrayDefaultMismatchCertificate {
    /// The top-level equality assertion that forces the two arrays equal.
    pub equality: TermId,
    /// Left array after resolving top-level array definitions.
    pub lhs_array: TermId,
    /// Right array after resolving top-level array definitions.
    pub rhs_array: TermId,
    /// Left constant-array default value.
    pub lhs_default: TermId,
    /// Right constant-array default value.
    pub rhs_default: TermId,
    /// Number of finite stores above the left constant-array base.
    pub lhs_writes: usize,
    /// Number of finite stores above the right constant-array base.
    pub rhs_writes: usize,
}

impl ConstArrayDefaultMismatchCertificate {
    /// Re-derives the certificate from the original assertions.
    #[must_use]
    pub fn recheck(&self, arena: &TermArena, assertions: &[TermId]) -> bool {
        const_array_default_mismatch_refutation(arena, assertions).as_ref() == Some(self)
    }
}

/// Returns a certificate for the constant-array finite-write mismatch described
/// by [`ConstArrayDefaultMismatchCertificate`], if present.
#[must_use]
pub fn const_array_default_mismatch_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<ConstArrayDefaultMismatchCertificate> {
    const_array_default_mismatch_refutation_within(arena, assertions, None)
}

pub fn const_array_default_mismatch_refutation_within(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Option<ConstArrayDefaultMismatchCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        if past_deadline(deadline) {
            return None;
        }
        collect_positive_conjuncts(arena, assertion, &mut conjuncts);
    }

    let defs = collect_array_symbol_definitions(arena, &conjuncts);
    for equality in conjuncts {
        if past_deadline(deadline) {
            return None;
        }
        let Some((lhs, rhs)) = array_equality(arena, equality) else {
            continue;
        };
        let lhs_array = resolve_array_definition(arena, lhs, &defs);
        let rhs_array = resolve_array_definition(arena, rhs, &defs);
        let Some(lhs_chain) = const_store_chain(arena, lhs_array, deadline) else {
            continue;
        };
        let Some(rhs_chain) = const_store_chain(arena, rhs_array, deadline) else {
            continue;
        };
        if lhs_chain.index != ArraySortKey::Int
            || rhs_chain.index != ArraySortKey::Int
            || arena.sort_of(lhs_array) != arena.sort_of(rhs_array)
        {
            continue;
        }
        if ground_constants_differ(arena, lhs_chain.default, rhs_chain.default) {
            return Some(ConstArrayDefaultMismatchCertificate {
                equality,
                lhs_array,
                rhs_array,
                lhs_default: lhs_chain.default,
                rhs_default: rhs_chain.default,
                lhs_writes: lhs_chain.writes,
                rhs_writes: rhs_chain.writes,
            });
        }
    }
    None
}

/// Which side of an array equality contains the visible store write used by a
/// [`StoreChainReadbackCertificate`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StoreChainSide {
    /// The selected visible write is on the equality's left-hand side.
    Left,
    /// The selected visible write is on the equality's right-hand side.
    Right,
}

/// A checked refutation for finite store-chain readback over `Array Int Int`.
///
/// If two store chains over the same base array are asserted equal, a visible
/// write `(store ... i v)` on one side forces the opposite side to read `v` at
/// `i`. When arithmetic aliases prove that `i` is distinct from every write
/// index on the opposite chain, the opposite read is exactly `(select base i)`;
/// an asserted disequality between `v` and that base read is therefore
/// impossible.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StoreChainReadbackCertificate {
    /// The top-level equality assertion connecting the two store chains.
    pub equality: TermId,
    /// Left array after resolving top-level array definitions.
    pub lhs_array: TermId,
    /// Right array after resolving top-level array definitions.
    pub rhs_array: TermId,
    /// Shared base array under both store chains.
    pub base_array: TermId,
    /// Side containing the visible write.
    pub write_side: StoreChainSide,
    /// Index of the visible write.
    pub write_index: TermId,
    /// Value written at [`Self::write_index`].
    pub write_value: TermId,
    /// The asserted-disequal term that resolves to `select(base_array, write_index)`.
    pub read_value: TermId,
    /// Number of stores above the left shared base.
    pub lhs_writes: usize,
    /// Number of stores above the right shared base.
    pub rhs_writes: usize,
}

impl StoreChainReadbackCertificate {
    /// Re-derives the certificate from the original assertions.
    #[must_use]
    pub fn recheck(&self, arena: &TermArena, assertions: &[TermId]) -> bool {
        store_chain_readback_refutation(arena, assertions).as_ref() == Some(self)
    }
}

/// Returns a certificate for the finite store-chain readback contradiction
/// described by [`StoreChainReadbackCertificate`], if present.
#[must_use]
pub fn store_chain_readback_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<StoreChainReadbackCertificate> {
    store_chain_readback_refutation_within(arena, assertions, None)
}

pub fn store_chain_readback_refutation_within(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Option<StoreChainReadbackCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        if past_deadline(deadline) {
            return None;
        }
        collect_positive_conjuncts(arena, assertion, &mut conjuncts);
    }

    let array_defs = collect_array_symbol_definitions(arena, &conjuncts);
    let scalar_defs = collect_int_symbol_definitions(arena, &conjuncts);
    let disequalities = collect_int_disequalities(arena, &conjuncts);
    if disequalities.is_empty() {
        return None;
    }

    for &equality in &conjuncts {
        if past_deadline(deadline) {
            return None;
        }
        let Some((lhs, rhs)) = array_equality(arena, equality) else {
            continue;
        };
        let lhs_array = resolve_array_definition(arena, lhs, &array_defs);
        let rhs_array = resolve_array_definition(arena, rhs, &array_defs);
        if !is_int_to_int_array(arena, lhs_array) || !is_int_to_int_array(arena, rhs_array) {
            continue;
        }
        let Some(lhs_chain) = store_chain(arena, lhs_array, &array_defs, deadline) else {
            continue;
        };
        let Some(rhs_chain) = store_chain(arena, rhs_array, &array_defs, deadline) else {
            continue;
        };
        if lhs_chain.base != rhs_chain.base
            || (lhs_chain.writes.is_empty() && rhs_chain.writes.is_empty())
        {
            continue;
        }
        if let Some(cert) = store_chain_readback_side(
            arena,
            &array_defs,
            &scalar_defs,
            &disequalities,
            equality,
            lhs_array,
            rhs_array,
            &lhs_chain,
            &rhs_chain,
            StoreChainSide::Left,
            deadline,
        ) {
            return Some(cert);
        }
        if let Some(cert) = store_chain_readback_side(
            arena,
            &array_defs,
            &scalar_defs,
            &disequalities,
            equality,
            lhs_array,
            rhs_array,
            &rhs_chain,
            &lhs_chain,
            StoreChainSide::Right,
            deadline,
        ) {
            return Some(cert);
        }
    }
    None
}

/// A checked refutation for same-index reciprocal stores followed by an array
/// disequality.
///
/// The core array consequence is:
///
/// ```text
/// store(A, i, select(B, i)) = store(B, i, select(A, i))  ==>  A = B
/// ```
///
/// The certificate checker iterates that consequence through nested store-chain
/// equalities, accepting only when it reaches an asserted direct disequality of
/// the derived base arrays. This covers declared-sort `QF_AX` rows where eager
/// finite-index extensionality and BV lowering are intentionally unavailable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CrossStoreArrayDisequalityCertificate {
    /// Left side of the final asserted array disequality.
    pub disequality_lhs: TermId,
    /// Right side of the final asserted array disequality.
    pub disequality_rhs: TermId,
    /// Number of reciprocal-store equality steps used to derive the refuted
    /// base-array equality.
    pub steps: usize,
}

impl CrossStoreArrayDisequalityCertificate {
    /// Re-derives the certificate from the original assertions.
    #[must_use]
    pub fn recheck(&self, arena: &TermArena, assertions: &[TermId]) -> bool {
        cross_store_array_disequality_refutation(arena, assertions).as_ref() == Some(self)
    }
}

/// Returns a certificate for a same-index reciprocal-store disequality
/// refutation, if present.
#[must_use]
pub fn cross_store_array_disequality_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<CrossStoreArrayDisequalityCertificate> {
    cross_store_array_disequality_refutation_within(arena, assertions, None)
}

pub fn cross_store_array_disequality_refutation_within(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Option<CrossStoreArrayDisequalityCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        if past_deadline(deadline) {
            return None;
        }
        collect_positive_conjuncts(arena, assertion, &mut conjuncts);
    }
    cross_store_array_disequality_refutation_from_conjuncts(arena, &conjuncts, deadline)
}

#[allow(clippy::too_many_arguments)]
fn store_chain_readback_side(
    arena: &TermArena,
    array_defs: &HashMap<SymbolId, Option<TermId>>,
    scalar_defs: &IntSymbolDefs,
    disequalities: &[(TermId, TermId)],
    equality: TermId,
    lhs_array: TermId,
    rhs_array: TermId,
    write_chain: &StoreChain,
    read_chain: &StoreChain,
    write_side: StoreChainSide,
    deadline: Option<Instant>,
) -> Option<StoreChainReadbackCertificate> {
    for (pos, write) in write_chain.writes.iter().enumerate() {
        if past_deadline(deadline) {
            return None;
        }
        if !write_is_visible(arena, scalar_defs, &write_chain.writes, pos) {
            continue;
        }
        if !read_index_untouched(arena, scalar_defs, write.index, &read_chain.writes) {
            continue;
        }
        let Some(read_value) = disequal_base_read(
            arena,
            array_defs,
            scalar_defs,
            disequalities,
            write.value,
            write_chain.base,
            write.index,
        ) else {
            continue;
        };
        return Some(StoreChainReadbackCertificate {
            equality,
            lhs_array,
            rhs_array,
            base_array: write_chain.base,
            write_side,
            write_index: write.index,
            write_value: write.value,
            read_value,
            lhs_writes: if write_side == StoreChainSide::Left {
                write_chain.writes.len()
            } else {
                read_chain.writes.len()
            },
            rhs_writes: if write_side == StoreChainSide::Left {
                read_chain.writes.len()
            } else {
                write_chain.writes.len()
            },
        });
    }
    None
}

#[derive(Clone, Copy)]
struct StoreWrite {
    index: TermId,
    value: TermId,
}

#[derive(Clone)]
struct StoreChain {
    base: TermId,
    writes: Vec<StoreWrite>,
}

fn store_chain(
    arena: &TermArena,
    term: TermId,
    defs: &HashMap<SymbolId, Option<TermId>>,
    deadline: Option<Instant>,
) -> Option<StoreChain> {
    if past_deadline(deadline) {
        return None;
    }
    let term = resolve_array_definition(arena, term, defs);
    match arena.node(term) {
        TermNode::App {
            op: Op::Store,
            args,
        } => {
            let [base, index, value] = &**args else {
                return None;
            };
            let mut chain = store_chain(arena, *base, defs, deadline)?;
            chain.writes.push(StoreWrite {
                index: *index,
                value: *value,
            });
            Some(chain)
        }
        _ if matches!(arena.sort_of(term), Sort::Array { .. }) => Some(StoreChain {
            base: term,
            writes: Vec::new(),
        }),
        _ => None,
    }
}

fn is_int_to_int_array(arena: &TermArena, term: TermId) -> bool {
    matches!(
        arena.sort_of(term),
        Sort::Array {
            index: ArraySortKey::Int,
            element: ArraySortKey::Int,
        }
    )
}

type IntSymbolDefs = HashMap<SymbolId, Option<(TermId, TermId)>>;

fn collect_int_symbol_definitions(arena: &TermArena, conjuncts: &[TermId]) -> IntSymbolDefs {
    let mut defs = HashMap::new();
    for &conjunct in conjuncts {
        let TermNode::App { op: Op::Eq, args } = arena.node(conjunct) else {
            continue;
        };
        let [lhs, rhs] = &**args else {
            continue;
        };
        collect_int_symbol_definition_side(arena, &mut defs, *lhs, *rhs);
        collect_int_symbol_definition_side(arena, &mut defs, *rhs, *lhs);
    }
    defs
}

fn collect_int_symbol_definition_side(
    arena: &TermArena,
    defs: &mut IntSymbolDefs,
    lhs: TermId,
    rhs: TermId,
) {
    let TermNode::Symbol(symbol) = arena.node(lhs) else {
        return;
    };
    if arena.sort_of(lhs) != Sort::Int || arena.sort_of(rhs) != Sort::Int {
        return;
    }
    if matches!(arena.node(rhs), TermNode::Symbol(_)) {
        return;
    }
    match defs.get_mut(symbol) {
        Some(slot) if *slot == Some((lhs, rhs)) => {}
        Some(slot) => *slot = None,
        None => {
            defs.insert(*symbol, Some((lhs, rhs)));
        }
    }
}

fn resolve_scalar_definition(arena: &TermArena, mut term: TermId, defs: &IntSymbolDefs) -> TermId {
    let mut seen = HashSet::new();
    loop {
        let TermNode::Symbol(symbol) = arena.node(term) else {
            return term;
        };
        if !seen.insert(*symbol) {
            return term;
        }
        match defs.get(symbol).copied().flatten() {
            Some((_symbol_term, body)) => term = body,
            None => return term,
        }
    }
}

fn collect_int_disequalities(arena: &TermArena, conjuncts: &[TermId]) -> Vec<(TermId, TermId)> {
    conjuncts
        .iter()
        .filter_map(|&term| int_disequality(arena, term))
        .collect()
}

fn int_disequality(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [eq] = &**args else {
        return None;
    };
    let TermNode::App {
        op: Op::Eq,
        args: eq_args,
    } = arena.node(*eq)
    else {
        return None;
    };
    let [lhs, rhs] = &**eq_args else {
        return None;
    };
    if arena.sort_of(*lhs) == Sort::Int && arena.sort_of(*rhs) == Sort::Int {
        Some((*lhs, *rhs))
    } else {
        None
    }
}

fn write_is_visible(
    arena: &TermArena,
    scalar_defs: &IntSymbolDefs,
    writes: &[StoreWrite],
    pos: usize,
) -> bool {
    let index = writes[pos].index;
    writes[(pos + 1)..]
        .iter()
        .all(|later| affine_distinct(arena, scalar_defs, index, later.index))
}

fn read_index_untouched(
    arena: &TermArena,
    scalar_defs: &IntSymbolDefs,
    index: TermId,
    writes: &[StoreWrite],
) -> bool {
    writes
        .iter()
        .all(|write| affine_distinct(arena, scalar_defs, index, write.index))
}

fn disequal_base_read(
    arena: &TermArena,
    array_defs: &HashMap<SymbolId, Option<TermId>>,
    scalar_defs: &IntSymbolDefs,
    disequalities: &[(TermId, TermId)],
    value: TermId,
    base: TermId,
    index: TermId,
) -> Option<TermId> {
    for &(lhs, rhs) in disequalities {
        if scalar_terms_equal(arena, scalar_defs, value, lhs)
            && term_is_base_read(arena, array_defs, scalar_defs, rhs, base, index)
        {
            return Some(rhs);
        }
        if scalar_terms_equal(arena, scalar_defs, value, rhs)
            && term_is_base_read(arena, array_defs, scalar_defs, lhs, base, index)
        {
            return Some(lhs);
        }
    }
    None
}

fn scalar_terms_equal(
    arena: &TermArena,
    scalar_defs: &IntSymbolDefs,
    lhs: TermId,
    rhs: TermId,
) -> bool {
    lhs == rhs
        || resolve_scalar_definition(arena, lhs, scalar_defs) == rhs
        || lhs == resolve_scalar_definition(arena, rhs, scalar_defs)
        || resolve_scalar_definition(arena, lhs, scalar_defs)
            == resolve_scalar_definition(arena, rhs, scalar_defs)
}

fn term_is_base_read(
    arena: &TermArena,
    array_defs: &HashMap<SymbolId, Option<TermId>>,
    scalar_defs: &IntSymbolDefs,
    term: TermId,
    base: TermId,
    index: TermId,
) -> bool {
    let term = resolve_scalar_definition(arena, term, scalar_defs);
    let Some((array, read_index)) = select_parts(arena, term) else {
        return false;
    };
    resolve_array_definition(arena, array, array_defs) == base
        && affine_equal(arena, scalar_defs, read_index, index)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct UnitAffine {
    base: Option<SymbolId>,
    coeff: i8,
    offset: i128,
}

impl UnitAffine {
    fn constant(offset: i128) -> Self {
        Self {
            base: None,
            coeff: 0,
            offset,
        }
    }

    fn var(symbol: SymbolId) -> Self {
        Self {
            base: Some(symbol),
            coeff: 1,
            offset: 0,
        }
    }

    fn neg(self) -> Option<Self> {
        Some(Self {
            base: self.base,
            coeff: self.coeff.checked_neg()?,
            offset: self.offset.checked_neg()?,
        })
    }

    fn add(self, rhs: Self) -> Option<Self> {
        let offset = self.offset.checked_add(rhs.offset)?;
        match (self.base, rhs.base) {
            (None, None) => Some(Self::constant(offset)),
            (Some(_), None) => Some(Self { offset, ..self }),
            (None, Some(_)) => Some(Self { offset, ..rhs }),
            (Some(a), Some(b)) if a == b => {
                let coeff = self.coeff.checked_add(rhs.coeff)?;
                if !(-1..=1).contains(&coeff) {
                    return None;
                }
                Some(if coeff == 0 {
                    Self::constant(offset)
                } else {
                    Self {
                        base: Some(a),
                        coeff,
                        offset,
                    }
                })
            }
            (Some(_), Some(_)) => None,
        }
    }

    fn sub(self, rhs: Self) -> Option<Self> {
        self.add(rhs.neg()?)
    }
}

fn affine_equal(arena: &TermArena, scalar_defs: &IntSymbolDefs, lhs: TermId, rhs: TermId) -> bool {
    lhs == rhs
        || matches!(
            (
                affine_index(arena, scalar_defs, lhs),
                affine_index(arena, scalar_defs, rhs)
            ),
            (Some(a), Some(b)) if a == b
        )
}

fn affine_distinct(
    arena: &TermArena,
    scalar_defs: &IntSymbolDefs,
    lhs: TermId,
    rhs: TermId,
) -> bool {
    matches!(
        (
            affine_index(arena, scalar_defs, lhs),
            affine_index(arena, scalar_defs, rhs)
        ),
        (Some(a), Some(b)) if a.base == b.base && a.coeff == b.coeff && a.offset != b.offset
    )
}

fn affine_index(
    arena: &TermArena,
    scalar_defs: &IntSymbolDefs,
    term: TermId,
) -> Option<UnitAffine> {
    let mut seen = HashSet::new();
    affine_index_rec(arena, scalar_defs, term, &mut seen)
}

fn affine_index_rec(
    arena: &TermArena,
    scalar_defs: &IntSymbolDefs,
    term: TermId,
    seen: &mut HashSet<SymbolId>,
) -> Option<UnitAffine> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(UnitAffine::constant(*value)),
        TermNode::Symbol(symbol) if arena.sort_of(term) == Sort::Int => {
            if let Some(Some((_symbol_term, body))) = scalar_defs.get(symbol) {
                if !seen.insert(*symbol) {
                    return None;
                }
                let result = affine_index_rec(arena, scalar_defs, *body, seen);
                seen.remove(symbol);
                result
            } else {
                Some(UnitAffine::var(*symbol))
            }
        }
        TermNode::App { op, args } => match op {
            Op::IntNeg => {
                let [arg] = &**args else {
                    return None;
                };
                affine_index_rec(arena, scalar_defs, *arg, seen)?.neg()
            }
            Op::IntAdd => {
                let [lhs, rhs] = &**args else {
                    return None;
                };
                affine_index_rec(arena, scalar_defs, *lhs, seen)?.add(affine_index_rec(
                    arena,
                    scalar_defs,
                    *rhs,
                    seen,
                )?)
            }
            Op::IntSub => {
                let [lhs, rhs] = &**args else {
                    return None;
                };
                affine_index_rec(arena, scalar_defs, *lhs, seen)?.sub(affine_index_rec(
                    arena,
                    scalar_defs,
                    *rhs,
                    seen,
                )?)
            }
            _ => None,
        },
        _ => None,
    }
}

#[derive(Clone, Copy)]
struct ConstStoreChain {
    index: ArraySortKey,
    default: TermId,
    writes: usize,
}

fn collect_array_symbol_definitions(
    arena: &TermArena,
    conjuncts: &[TermId],
) -> HashMap<SymbolId, Option<TermId>> {
    let mut defs = HashMap::new();
    for &conjunct in conjuncts {
        let Some((lhs, rhs)) = array_equality(arena, conjunct) else {
            continue;
        };
        collect_array_symbol_definition_side(arena, &mut defs, lhs, rhs);
        collect_array_symbol_definition_side(arena, &mut defs, rhs, lhs);
    }
    defs
}

fn collect_array_symbol_definition_side(
    arena: &TermArena,
    defs: &mut HashMap<SymbolId, Option<TermId>>,
    lhs: TermId,
    rhs: TermId,
) {
    let TermNode::Symbol(symbol) = arena.node(lhs) else {
        return;
    };
    if !matches!(arena.sort_of(lhs), Sort::Array { .. }) || arena.sort_of(lhs) != arena.sort_of(rhs)
    {
        return;
    }
    if matches!(arena.node(rhs), TermNode::Symbol(_)) {
        return;
    }
    match defs.get_mut(symbol) {
        Some(slot) if *slot == Some(rhs) => {}
        Some(slot) => *slot = None,
        None => {
            defs.insert(*symbol, Some(rhs));
        }
    }
}

fn resolve_array_definition(
    arena: &TermArena,
    mut term: TermId,
    defs: &HashMap<SymbolId, Option<TermId>>,
) -> TermId {
    let mut seen = HashSet::new();
    loop {
        let TermNode::Symbol(symbol) = arena.node(term) else {
            return term;
        };
        if !seen.insert(*symbol) {
            return term;
        }
        match defs.get(symbol).copied().flatten() {
            Some(next) => term = next,
            None => return term,
        }
    }
}

fn array_equality(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    if matches!(arena.sort_of(*lhs), Sort::Array { .. })
        && arena.sort_of(*lhs) == arena.sort_of(*rhs)
    {
        Some((*lhs, *rhs))
    } else {
        None
    }
}

fn const_store_chain(
    arena: &TermArena,
    term: TermId,
    deadline: Option<Instant>,
) -> Option<ConstStoreChain> {
    if past_deadline(deadline) {
        return None;
    }
    match arena.node(term) {
        TermNode::App {
            op: Op::ConstArray { index },
            args,
        } => {
            let [default] = &**args else {
                return None;
            };
            Some(ConstStoreChain {
                index: *index,
                default: *default,
                writes: 0,
            })
        }
        TermNode::App {
            op: Op::Store,
            args,
        } => {
            let [base, _idx, _value] = &**args else {
                return None;
            };
            let mut chain = const_store_chain(arena, *base, deadline)?;
            chain.writes = chain.writes.checked_add(1)?;
            Some(chain)
        }
        _ => None,
    }
}

fn ground_constants_differ(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    if lhs == rhs || arena.sort_of(lhs) != arena.sort_of(rhs) {
        return false;
    }
    match (arena.node(lhs), arena.node(rhs)) {
        (TermNode::BoolConst(a), TermNode::BoolConst(b)) => a != b,
        (
            TermNode::BvConst {
                width: wa,
                value: va,
            },
            TermNode::BvConst {
                width: wb,
                value: vb,
            },
        ) => wa == wb && va != vb,
        (TermNode::WideBvConst(a), TermNode::WideBvConst(b)) => a != b,
        (TermNode::IntConst(a), TermNode::IntConst(b)) => a != b,
        (TermNode::RealConst(a), TermNode::RealConst(b)) => a != b,
        _ => false,
    }
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

    if cross_store_array_disequality_refutation_from_conjuncts(arena, &conjuncts, deadline)
        .is_some()
    {
        return true;
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

fn cross_store_array_disequality_refutation_from_conjuncts(
    arena: &TermArena,
    conjuncts: &[TermId],
    deadline: Option<Instant>,
) -> Option<CrossStoreArrayDisequalityCertificate> {
    let disequalities: Vec<(TermId, TermId)> = conjuncts
        .iter()
        .filter_map(|&term| negated_array_equality(arena, term))
        .map(canonical_term_pair)
        .collect();
    if disequalities.is_empty() {
        return None;
    }

    let mut work: Vec<((TermId, TermId), usize)> = conjuncts
        .iter()
        .filter_map(|&term| positive_array_equality(arena, term))
        .map(|pair| (pair, 0))
        .collect();
    let mut seen = BTreeSet::new();

    while let Some(((lhs, rhs), steps)) = work.pop() {
        if past_deadline(deadline) {
            return None;
        }
        let pair = canonical_term_pair((lhs, rhs));
        if !seen.insert(pair) {
            continue;
        }
        if steps > 0 && disequalities.contains(&pair) {
            return Some(CrossStoreArrayDisequalityCertificate {
                disequality_lhs: pair.0,
                disequality_rhs: pair.1,
                steps,
            });
        }
        if let Some(base_pair) = cross_store_base_equality(arena, lhs, rhs) {
            work.push((base_pair, steps + 1));
        }
    }

    None
}

fn positive_array_equality(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    array_equality_args(arena, args[0], args[1])
}

fn negated_array_equality(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    positive_array_equality(arena, args[0])
}

fn array_equality_args(arena: &TermArena, lhs: TermId, rhs: TermId) -> Option<(TermId, TermId)> {
    if matches!(arena.sort_of(lhs), Sort::Array { .. }) && arena.sort_of(lhs) == arena.sort_of(rhs)
    {
        Some((lhs, rhs))
    } else {
        None
    }
}

fn canonical_term_pair((lhs, rhs): (TermId, TermId)) -> (TermId, TermId) {
    if lhs <= rhs { (lhs, rhs) } else { (rhs, lhs) }
}

fn cross_store_base_equality(
    arena: &TermArena,
    lhs: TermId,
    rhs: TermId,
) -> Option<(TermId, TermId)> {
    let lhs = store_same_index_read_parts(arena, lhs)?;
    let rhs = store_same_index_read_parts(arena, rhs)?;
    if lhs.index == rhs.index && lhs.selected_array == rhs.base && rhs.selected_array == lhs.base {
        Some((lhs.base, rhs.base))
    } else {
        None
    }
}

#[derive(Clone, Copy)]
struct StoreSameIndexRead {
    base: TermId,
    index: TermId,
    selected_array: TermId,
}

fn store_same_index_read_parts(arena: &TermArena, term: TermId) -> Option<StoreSameIndexRead> {
    let TermNode::App {
        op: Op::Store,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let base = args[0];
    let index = args[1];
    let (selected_array, selected_index) = select_parts(arena, args[2])?;
    if index == selected_index {
        Some(StoreSameIndexRead {
            base,
            index,
            selected_array,
        })
    } else {
        None
    }
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

struct DeclaredSortEufBackend;

impl SolverBackend for DeclaredSortEufBackend {
    fn capabilities(&self) -> Capabilities {
        Capabilities {
            name: "declared-sort-euf".to_owned(),
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
        Ok(crate::euf_egraph::check_qf_uf_with_config(
            &mut scratch,
            assertions,
            config,
        ))
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

fn direct_array_symbol(arena: &TermArena, term: TermId) -> Option<SymbolId> {
    let TermNode::Symbol(symbol) = arena.node(term) else {
        return None;
    };
    if matches!(arena.sort_of(term), Sort::Array { .. }) {
        Some(*symbol)
    } else {
        None
    }
}

fn direct_select_repair_target(
    arena: &TermArena,
    term: TermId,
) -> Option<(SymbolId, TermId, TermId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let lhs = select_parts(arena, args[0]).and_then(|(array, index)| {
        direct_array_symbol(arena, array).map(|symbol| (symbol, index, args[1]))
    });
    let rhs = select_parts(arena, args[1]).and_then(|(array, index)| {
        direct_array_symbol(arena, array).map(|symbol| (symbol, index, args[0]))
    });
    match (lhs, rhs) {
        (Some(target), None) | (None, Some(target)) => Some(target),
        // Two-select equalities should be handled by congruence; choosing one side
        // here can oscillate between arrays under an incomplete scalar candidate.
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct ProjectionRepairStats {
    candidates: usize,
    array_changes: usize,
    symbol_changes: usize,
    branch_candidates: usize,
    branch_symbol_changes: usize,
    scalar_candidates: usize,
    scalar_support_candidates: usize,
    scalar_stabilized_trials: usize,
    scalar_rejected_worse_trials: usize,
    scalar_equal_support_repairs: usize,
    scalar_symbol_changes: usize,
}

impl ProjectionRepairStats {
    fn changes(self) -> usize {
        self.array_changes
            + self.symbol_changes
            + self.branch_symbol_changes
            + self.scalar_symbol_changes
    }

    fn absorb(&mut self, other: Self) {
        self.candidates += other.candidates;
        self.array_changes += other.array_changes;
        self.symbol_changes += other.symbol_changes;
        self.branch_candidates += other.branch_candidates;
        self.branch_symbol_changes += other.branch_symbol_changes;
        self.scalar_candidates += other.scalar_candidates;
        self.scalar_support_candidates += other.scalar_support_candidates;
        self.scalar_stabilized_trials += other.scalar_stabilized_trials;
        self.scalar_rejected_worse_trials += other.scalar_rejected_worse_trials;
        self.scalar_equal_support_repairs += other.scalar_equal_support_repairs;
        self.scalar_symbol_changes += other.scalar_symbol_changes;
    }
}

fn store_projected_array_entry(
    arena: &TermArena,
    projected: &mut Assignment,
    array: SymbolId,
    index: Value,
    element: Value,
) -> Result<bool, SolverError> {
    let sort = arena.symbol(array).1;
    if let Some((index_width, element_width)) = sort.array_widths() {
        let (_, index_value) = index.as_bv().ok_or_else(|| {
            SolverError::Backend("array repair expected a bit-vector index".to_owned())
        })?;
        let (_, element_value) = element.as_bv().ok_or_else(|| {
            SolverError::Backend("array repair expected a bit-vector element".to_owned())
        })?;
        let current = match projected.get(array) {
            Some(Value::Array(value)) => value.clone(),
            Some(other) => {
                return Err(SolverError::Backend(format!(
                    "array repair expected a bit-vector array, got {other}"
                )));
            }
            None => ArrayValue::constant(index_width, element_width, 0),
        };
        if current.select(index_value) == element_value {
            return Ok(false);
        }
        projected.set(
            array,
            Value::Array(current.store(index_value, element_value)),
        );
        return Ok(true);
    }

    let Sort::Array {
        index: index_key,
        element: element_key,
    } = sort
    else {
        return Err(SolverError::Backend(
            "array repair requested for a non-array symbol".to_owned(),
        ));
    };
    let expected_index_sort = index_key.to_sort();
    let expected_element_sort = element_key.to_sort();
    if index.sort() != expected_index_sort {
        return Err(SolverError::Backend(format!(
            "array repair index sort mismatch: expected {expected_index_sort}, got {}",
            index.sort()
        )));
    }
    if element.sort() != expected_element_sort {
        return Err(SolverError::Backend(format!(
            "array repair element sort mismatch: expected {expected_element_sort}, got {}",
            element.sort()
        )));
    }
    let current = match projected.get(array) {
        Some(Value::GenericArray(value)) => value.clone(),
        Some(other) => {
            return Err(SolverError::Backend(format!(
                "array repair expected a generic array, got {other}"
            )));
        }
        None => {
            let default = well_founded_default(arena, expected_element_sort).ok_or_else(|| {
                SolverError::Backend(
                    "array repair could not construct a default element value".to_owned(),
                )
            })?;
            GenericArrayValue::constant(index_key, element_key, default)
        }
    };
    if current.select(&index) == element {
        return Ok(false);
    }
    projected.set(array, Value::GenericArray(current.store(index, element)));
    Ok(true)
}

#[derive(Clone)]
struct ProjectionRepairDemand {
    element: Value,
    element_symbol: Option<SymbolId>,
}

struct ProjectionRepairGroup {
    array: SymbolId,
    index: Value,
    demands: Vec<ProjectionRepairDemand>,
}

fn direct_value_symbol(arena: &TermArena, term: TermId) -> Option<SymbolId> {
    let TermNode::Symbol(symbol) = arena.node(term) else {
        return None;
    };
    Some(*symbol)
}

fn add_projection_repair_demand(
    groups: &mut Vec<ProjectionRepairGroup>,
    array: SymbolId,
    index: Value,
    element: Value,
    element_symbol: Option<SymbolId>,
) {
    if let Some(group) = groups
        .iter_mut()
        .find(|group| group.array == array && group.index == index)
    {
        group.demands.push(ProjectionRepairDemand {
            element,
            element_symbol,
        });
    } else {
        groups.push(ProjectionRepairGroup {
            array,
            index,
            demands: vec![ProjectionRepairDemand {
                element,
                element_symbol,
            }],
        });
    }
}

fn repair_projected_arrays_from_asserted_select_equalities(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
) -> Result<ProjectionRepairStats, SolverError> {
    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext projection repair failed: {e}"))
    };
    let mut stats = ProjectionRepairStats::default();
    let mut groups: Vec<ProjectionRepairGroup> = Vec::new();
    let mut conjuncts = Vec::new();
    for &assertion in originals {
        conjuncts.clear();
        collect_positive_conjuncts(arena, assertion, &mut conjuncts);
        for &conjunct in &conjuncts {
            let Some((array, index_term, element_term)) =
                direct_select_repair_target(arena, conjunct)
            else {
                continue;
            };
            stats.candidates += 1;
            let index = eval(arena, index_term, projected).map_err(ir)?;
            let element = eval(arena, element_term, projected).map_err(ir)?;
            add_projection_repair_demand(
                &mut groups,
                array,
                index,
                element,
                direct_value_symbol(arena, element_term),
            );
        }
    }
    for group in groups {
        let Some(representative) = group.demands.first().map(|demand| demand.element.clone())
        else {
            continue;
        };
        if store_projected_array_entry(
            arena,
            projected,
            group.array,
            group.index,
            representative.clone(),
        )? {
            stats.array_changes += 1;
        }
        for demand in group.demands {
            let Some(symbol) = demand.element_symbol else {
                continue;
            };
            if projected.get(symbol) != Some(representative.clone()) {
                projected.set(symbol, representative.clone());
                stats.symbol_changes += 1;
            }
        }
    }
    Ok(stats)
}

fn align_direct_select_symbols_for_array(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
    array_symbol: SymbolId,
) -> Result<usize, SolverError> {
    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext branch readback repair failed: {e}"))
    };
    let array_value = projected
        .get(array_symbol)
        .unwrap_or(default_value_for_symbol(arena, array_symbol)?);
    let mut changes = 0;
    let mut conjuncts = Vec::new();
    for &assertion in originals {
        conjuncts.clear();
        collect_positive_conjuncts(arena, assertion, &mut conjuncts);
        for &conjunct in &conjuncts {
            let Some((array, index_term, element_term)) =
                direct_select_repair_target(arena, conjunct)
            else {
                continue;
            };
            if array != array_symbol {
                continue;
            }
            let Some(element_symbol) = direct_value_symbol(arena, element_term) else {
                continue;
            };
            let index = eval(arena, index_term, projected).map_err(ir)?;
            let element = select_value(&array_value, &index)?;
            if store_projected_symbol_value(arena, projected, element_symbol, element)? {
                changes += 1;
            }
        }
    }
    Ok(changes)
}

fn align_all_direct_select_symbols(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
) -> Result<usize, SolverError> {
    let mut changes = 0;
    for (symbol, _name, sort) in arena.symbols() {
        if matches!(sort, Sort::Array { .. }) {
            changes += align_direct_select_symbols_for_array(arena, originals, projected, symbol)?;
        }
    }
    Ok(changes)
}

fn direct_array_equality_repair_target(
    arena: &TermArena,
    term: TermId,
) -> Option<(SymbolId, SymbolId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let lhs = direct_array_symbol(arena, args[0])?;
    let rhs = direct_array_symbol(arena, args[1])?;
    (lhs != rhs).then_some((lhs, rhs))
}

fn array_entry_count(value: &Value) -> Result<usize, SolverError> {
    match value {
        Value::Array(array) => Ok(array.entries().count()),
        Value::GenericArray(array) => Ok(array.entries().count()),
        other => Err(SolverError::Backend(format!(
            "array equality repair expected an array value, got {other}"
        ))),
    }
}

fn direct_select_support_score(
    arena: &TermArena,
    originals: &[TermId],
    projected: &Assignment,
    array_symbol: SymbolId,
    array_value: &Value,
) -> Result<usize, SolverError> {
    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!(
            "lazy-ext branch array equality support failed: {e}"
        ))
    };
    let mut score = 0;
    let mut conjuncts = Vec::new();
    for &assertion in originals {
        conjuncts.clear();
        collect_positive_conjuncts(arena, assertion, &mut conjuncts);
        for &conjunct in &conjuncts {
            let Some((array, index_term, element_term)) =
                direct_select_repair_target(arena, conjunct)
            else {
                continue;
            };
            if array != array_symbol {
                continue;
            }
            let index = eval(arena, index_term, projected).map_err(ir)?;
            let element = eval(arena, element_term, projected).map_err(ir)?;
            if select_value(array_value, &index)? == element {
                score += 1;
            }
        }
    }
    Ok(score)
}

fn scalar_select_support_score(
    arena: &TermArena,
    originals: &[TermId],
    projected: &Assignment,
    symbol: SymbolId,
) -> Result<usize, SolverError> {
    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext scalar support scoring failed: {e}"))
    };
    let mut score = 0;
    let mut conjuncts = Vec::new();
    for &assertion in originals {
        conjuncts.clear();
        collect_positive_conjuncts(arena, assertion, &mut conjuncts);
        for &conjunct in &conjuncts {
            let Some((array, index_term, element_term)) =
                direct_select_repair_target(arena, conjunct)
            else {
                continue;
            };
            if direct_value_symbol(arena, element_term) != Some(symbol) {
                continue;
            }
            let array_value = projected
                .get(array)
                .unwrap_or(default_value_for_symbol(arena, array)?);
            let index = eval(arena, index_term, projected).map_err(ir)?;
            let element = eval(arena, element_term, projected).map_err(ir)?;
            if select_value(&array_value, &index)? == element {
                score += 1;
            }
        }
    }
    Ok(score)
}

fn array_equality_repair_key(
    arena: &TermArena,
    originals: &[TermId],
    projected: &Assignment,
    array_symbol: SymbolId,
    array_value: &Value,
) -> Result<(usize, usize), SolverError> {
    Ok((
        array_entry_count(array_value)?,
        direct_select_support_score(arena, originals, projected, array_symbol, array_value)?,
    ))
}

fn compact_replay_value(value: &Value) -> String {
    const LIMIT: usize = 120;
    let rendered = value.to_string();
    if rendered.chars().count() <= LIMIT {
        rendered
    } else {
        let prefix = rendered.chars().take(LIMIT).collect::<String>();
        format!("{prefix}...")
    }
}

fn replay_failed_eq_details(
    arena: &TermArena,
    conjunct: TermId,
    assignment: &Assignment,
) -> Result<Option<ReplayEqFailure>, SolverError> {
    let TermNode::App { op: Op::Eq, args } = arena.node(conjunct) else {
        return Ok(None);
    };
    let ir = |error| SolverError::Backend(format!("lazy-ext replay eq detail failed: {error}"));
    let lhs = eval(arena, args[0], assignment).map_err(ir)?;
    let rhs = eval(arena, args[1], assignment).map_err(ir)?;
    Ok(Some(ReplayEqFailure {
        lhs_term: args[0],
        rhs_term: args[1],
        lhs_value: compact_replay_value(&lhs),
        rhs_value: compact_replay_value(&rhs),
    }))
}

fn collect_positive_disjuncts(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolOr,
            args,
        } => {
            for &arg in args {
                collect_positive_disjuncts(arena, arg, out);
            }
        }
        _ => out.push(term),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReplayOrFailure {
    branch_count: usize,
    best_branch_term: TermId,
    best_branch_ordinal: usize,
    best_branch_false_literals: usize,
    best_branch_total_literals: usize,
    best_branch_first_false_term: Option<TermId>,
    best_branch_first_false_eq: Option<ReplayEqFailure>,
    best_branch_false_literal_details: Vec<ReplayBranchFalseLiteralDiagnostic>,
    best_branch_paired_scalar_chain: Option<ReplayScalarChainDiagnostic>,
    scalar_closure_branch_candidates: Vec<ReplayBranchScalarClosureCandidateDiagnostic>,
}

fn replay_failed_or_details(
    arena: &TermArena,
    conjunct: TermId,
    assignment: &Assignment,
) -> Result<Option<ReplayOrFailure>, SolverError> {
    const MAX_BRANCH_FALSE_LITERAL_DETAILS: usize = 4;

    if !matches!(arena.node(conjunct), TermNode::App { op: Op::BoolOr, .. }) {
        return Ok(None);
    }

    let mut branches = Vec::new();
    collect_positive_disjuncts(arena, conjunct, &mut branches);
    if branches.is_empty() {
        return Ok(None);
    }

    let mut best: Option<ReplayOrFailure> = None;
    let mut literals = Vec::new();
    for (branch_ordinal, &branch) in branches.iter().enumerate() {
        literals.clear();
        collect_positive_conjuncts(arena, branch, &mut literals);
        let mut false_literals = 0usize;
        let mut first_false = None;
        let mut false_literal_details = Vec::new();
        for &literal in &literals {
            match eval(arena, literal, assignment) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => {
                    false_literals += 1;
                    first_false.get_or_insert(literal);
                    if false_literal_details.len() < MAX_BRANCH_FALSE_LITERAL_DETAILS {
                        false_literal_details.push(ReplayBranchFalseLiteralDiagnostic {
                            literal_term: literal,
                            eq: replay_failed_eq_details(arena, literal, assignment)?,
                            scalar_choices: Vec::new(),
                        });
                    }
                }
                Ok(value) => {
                    return Err(SolverError::Backend(format!(
                        "lazy-ext replay: branch literal #{} evaluated to non-Boolean {value}",
                        literal.index()
                    )));
                }
                Err(error) => {
                    return Err(SolverError::Backend(format!(
                        "lazy-ext replay: branch literal #{} failed evaluation: {error}",
                        literal.index()
                    )));
                }
            }
        }
        let candidate = ReplayOrFailure {
            branch_count: branches.len(),
            best_branch_term: branch,
            best_branch_ordinal: branch_ordinal,
            best_branch_false_literals: false_literals,
            best_branch_total_literals: literals.len(),
            best_branch_first_false_term: first_false,
            best_branch_first_false_eq: match first_false {
                Some(term) => replay_failed_eq_details(arena, term, assignment)?,
                None => None,
            },
            best_branch_false_literal_details: false_literal_details,
            best_branch_paired_scalar_chain: None,
            scalar_closure_branch_candidates: Vec::new(),
        };
        let candidate_key = (
            candidate.best_branch_false_literals,
            candidate.best_branch_total_literals,
            candidate.best_branch_ordinal,
        );
        let replace = best.as_ref().is_none_or(|current| {
            candidate_key
                < (
                    current.best_branch_false_literals,
                    current.best_branch_total_literals,
                    current.best_branch_ordinal,
                )
        });
        if replace {
            best = Some(candidate);
        }
    }
    Ok(best)
}

fn direct_symbol_equality_repair_target(
    arena: &TermArena,
    term: TermId,
) -> Option<(SymbolId, TermId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    match (
        direct_value_symbol(arena, args[0]),
        direct_value_symbol(arena, args[1]),
    ) {
        (Some(symbol), None) => Some((symbol, args[1])),
        (None, Some(symbol)) => Some((symbol, args[0])),
        // Direct symbol-to-symbol equalities are better handled by the scalar
        // model; choosing a direction here can perturb unrelated equalities.
        _ => None,
    }
}

fn direct_scalar_equality_repair_target(
    arena: &TermArena,
    term: TermId,
) -> Option<(SymbolId, TermId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    match (
        direct_value_symbol(arena, args[0]),
        direct_value_symbol(arena, args[1]),
    ) {
        (Some(symbol), Some(_) | None) if !matches!(arena.symbol(symbol).1, Sort::Array { .. }) => {
            Some((symbol, args[1]))
        }
        (None, Some(symbol)) if !matches!(arena.symbol(symbol).1, Sort::Array { .. }) => {
            Some((symbol, args[0]))
        }
        _ => None,
    }
}

fn direct_scalar_equality_repair_choices(
    arena: &TermArena,
    term: TermId,
) -> Vec<(SymbolId, TermId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return Vec::new();
    };
    let lhs = direct_value_symbol(arena, args[0])
        .filter(|symbol| !matches!(arena.symbol(*symbol).1, Sort::Array { .. }));
    let rhs = direct_value_symbol(arena, args[1])
        .filter(|symbol| !matches!(arena.symbol(*symbol).1, Sort::Array { .. }));
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) if lhs != rhs => vec![(lhs, args[1]), (rhs, args[0])],
        (Some(lhs), _) => vec![(lhs, args[1])],
        (_, Some(rhs)) => vec![(rhs, args[0])],
        _ => Vec::new(),
    }
}

fn replay_scalar_choice_diagnostics_for_literal(
    arena: &TermArena,
    originals: &[TermId],
    branch: TermId,
    assignment: &Assignment,
    literal: TermId,
) -> Result<Vec<ReplayScalarChoiceDiagnostic>, SolverError> {
    const MAX_SCALAR_CHOICE_DIAGNOSTICS: usize = 4;

    let mut diagnostics = Vec::new();
    for (target_symbol, value_term) in direct_scalar_equality_repair_choices(arena, literal)
        .into_iter()
        .take(MAX_SCALAR_CHOICE_DIAGNOSTICS)
    {
        let (diagnostic, _) = replay_scalar_choice_effect(
            arena,
            originals,
            branch,
            assignment,
            literal,
            target_symbol,
            value_term,
        )?;
        diagnostics.push(diagnostic);
    }
    Ok(diagnostics)
}

fn replay_scalar_choice_effect(
    arena: &TermArena,
    originals: &[TermId],
    branch: TermId,
    assignment: &Assignment,
    literal: TermId,
    target_symbol: SymbolId,
    value_term: TermId,
) -> Result<(ReplayScalarChoiceDiagnostic, Assignment), SolverError> {
    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext scalar choice diagnostic failed: {e}"))
    };
    let value = eval(arena, value_term, assignment).map_err(ir)?;
    let mut trial = assignment.clone();
    let changed = store_projected_symbol_value(arena, &mut trial, target_symbol, value.clone())?;
    let literal_true = eval(arena, literal, &trial).map_err(ir)? == Value::Bool(true);
    let branch_false_literals = branch_false_literal_count(arena, branch, &trial)?;
    let total_false_conjuncts = positive_replay_false_count(arena, originals, &trial)?;
    let global_failure =
        first_projected_replay_failure(arena, originals, &trial, ProjectionRepairStats::default())?;
    Ok((
        ReplayScalarChoiceDiagnostic {
            target_symbol,
            value_term,
            value: compact_replay_value(&value),
            changed,
            literal_true,
            branch_false_literals,
            total_false_conjuncts,
            first_global_false_ordinal: global_failure
                .as_ref()
                .map(|failure| failure.conjunct_ordinal),
            first_global_false_term: global_failure.as_ref().map(|failure| failure.conjunct_term),
            first_global_false_eq: global_failure
                .as_ref()
                .and_then(|failure| failure.failed_eq.clone()),
        },
        trial,
    ))
}

fn replay_best_scalar_choice_effect_for_literal(
    arena: &TermArena,
    originals: &[TermId],
    branch: TermId,
    assignment: &Assignment,
    literal: TermId,
) -> Result<Option<(ReplayScalarChoiceDiagnostic, Assignment)>, SolverError> {
    let mut best: Option<(
        usize,
        usize,
        usize,
        ReplayScalarChoiceDiagnostic,
        Assignment,
    )> = None;
    for (ordinal, (target_symbol, value_term)) in
        direct_scalar_equality_repair_choices(arena, literal)
            .into_iter()
            .enumerate()
    {
        let (diagnostic, trial) = replay_scalar_choice_effect(
            arena,
            originals,
            branch,
            assignment,
            literal,
            target_symbol,
            value_term,
        )?;
        if !diagnostic.changed || !diagnostic.literal_true {
            continue;
        }
        let replace = best.as_ref().is_none_or(
            |(best_branch_false, best_total_false, best_ordinal, _, _)| {
                (
                    diagnostic.branch_false_literals,
                    diagnostic.total_false_conjuncts,
                    ordinal,
                ) < (*best_branch_false, *best_total_false, *best_ordinal)
            },
        );
        if replace {
            best = Some((
                diagnostic.branch_false_literals,
                diagnostic.total_false_conjuncts,
                ordinal,
                diagnostic,
                trial,
            ));
        }
    }
    Ok(best.map(|(_, _, _, diagnostic, trial)| (diagnostic, trial)))
}

fn replay_paired_scalar_chain_diagnostic_for_or_failure(
    arena: &TermArena,
    originals: &[TermId],
    assignment: &Assignment,
    or_failure: &ReplayOrFailure,
) -> Result<Option<ReplayScalarChainDiagnostic>, SolverError> {
    const MAX_PAIRED_SCALAR_CHAIN_LITERALS: usize = 4;
    const MAX_PAIRED_SCALAR_CHAIN_FOLLOWUPS: usize = 4;

    let scalar_false_literals = or_failure
        .best_branch_false_literal_details
        .iter()
        .filter(|detail| {
            !direct_scalar_equality_repair_choices(arena, detail.literal_term).is_empty()
        })
        .take(MAX_PAIRED_SCALAR_CHAIN_LITERALS + 1)
        .map(|detail| detail.literal_term)
        .collect::<Vec<_>>();
    if !(2..=MAX_PAIRED_SCALAR_CHAIN_LITERALS).contains(&scalar_false_literals.len()) {
        return Ok(None);
    }

    let mut trial = assignment.clone();
    let mut branch_steps = Vec::new();
    for literal in scalar_false_literals {
        if eval(arena, literal, &trial).map_err(|error| {
            SolverError::Backend(format!("lazy-ext paired scalar diagnostic failed: {error}"))
        })? == Value::Bool(true)
        {
            continue;
        }
        let Some((diagnostic, next_trial)) = replay_best_scalar_choice_effect_for_literal(
            arena,
            originals,
            or_failure.best_branch_term,
            &trial,
            literal,
        )?
        else {
            return Ok(None);
        };
        branch_steps.push(diagnostic);
        trial = next_trial;
    }
    if branch_steps.len() < 2 {
        return Ok(None);
    }

    let mut followup_steps = Vec::new();
    let mut seen_followups = BTreeSet::new();
    for _ in 0..MAX_PAIRED_SCALAR_CHAIN_FOLLOWUPS {
        let Some(failure) = first_projected_replay_failure(
            arena,
            originals,
            &trial,
            ProjectionRepairStats::default(),
        )?
        else {
            break;
        };
        if !seen_followups.insert(failure.conjunct_ordinal)
            || direct_scalar_equality_repair_choices(arena, failure.conjunct_term).is_empty()
        {
            break;
        }
        let Some((diagnostic, next_trial)) = replay_best_scalar_choice_effect_for_literal(
            arena,
            originals,
            or_failure.best_branch_term,
            &trial,
            failure.conjunct_term,
        )?
        else {
            break;
        };
        followup_steps.push(diagnostic);
        trial = next_trial;
    }

    let final_branch_false =
        branch_false_literal_count(arena, or_failure.best_branch_term, &trial)?;
    let final_total_false = positive_replay_false_count(arena, originals, &trial)?;
    let final_failure =
        first_projected_replay_failure(arena, originals, &trial, ProjectionRepairStats::default())?;
    Ok(Some(ReplayScalarChainDiagnostic {
        branch_steps,
        followup_steps,
        final_branch_false_literals: final_branch_false,
        final_total_false_conjuncts: final_total_false,
        final_global_false_ordinal: final_failure
            .as_ref()
            .map(|failure| failure.conjunct_ordinal),
        final_global_false_term: final_failure.as_ref().map(|failure| failure.conjunct_term),
        final_global_false_eq: final_failure
            .as_ref()
            .and_then(|failure| failure.failed_eq.clone()),
    }))
}

fn replay_scalar_closure_from_trial(
    arena: &TermArena,
    originals: &[TermId],
    branch: TermId,
    assignment: &Assignment,
) -> Result<(Vec<ReplayScalarChoiceDiagnostic>, Assignment), SolverError> {
    const MAX_SCALAR_CLOSURE_STEPS: usize = 4;

    let mut trial = assignment.clone();
    let mut steps = Vec::new();
    let mut seen = BTreeSet::new();
    for _ in 0..MAX_SCALAR_CLOSURE_STEPS {
        let Some(failure) = first_projected_replay_failure(
            arena,
            originals,
            &trial,
            ProjectionRepairStats::default(),
        )?
        else {
            break;
        };
        if !seen.insert(failure.conjunct_ordinal)
            || direct_scalar_equality_repair_choices(arena, failure.conjunct_term).is_empty()
        {
            break;
        }
        let Some((diagnostic, next_trial)) = replay_best_scalar_choice_effect_for_literal(
            arena,
            originals,
            branch,
            &trial,
            failure.conjunct_term,
        )?
        else {
            break;
        };
        steps.push(diagnostic);
        trial = next_trial;
    }
    Ok((steps, trial))
}

#[allow(clippy::too_many_lines)]
fn replay_scalar_closure_branch_candidates(
    arena: &TermArena,
    originals: &[TermId],
    assignment: &Assignment,
    disjunction: TermId,
    or_failure: &ReplayOrFailure,
) -> Result<Vec<ReplayBranchScalarClosureCandidateDiagnostic>, SolverError> {
    const MAX_SCALAR_CLOSURE_BRANCHES: usize = 32;
    const MAX_SCALAR_CLOSURE_REPORTED_BRANCHES: usize = 8;

    if or_failure.best_branch_false_literals < 2
        || or_failure.branch_count > MAX_SCALAR_CLOSURE_BRANCHES
        || or_failure
            .best_branch_false_literal_details
            .iter()
            .all(|detail| {
                direct_scalar_equality_repair_choices(arena, detail.literal_term).is_empty()
            })
    {
        return Ok(Vec::new());
    }

    let mut branches = Vec::new();
    collect_positive_disjuncts(arena, disjunction, &mut branches);
    let mut diagnostics = Vec::new();
    for (branch_ordinal, branch) in branches.into_iter().enumerate() {
        let initial_false = branch_false_literal_count(arena, branch, assignment)?;
        let mut trial = assignment.clone();
        let (repair_kind, repair_changes) = if initial_false == 0 {
            ("already_true".to_owned(), 0)
        } else if let Some((kind, stats)) =
            repair_projected_branch_best_candidate(arena, originals, branch, &mut trial)?
        {
            (kind.to_owned(), stats.changes())
        } else {
            diagnostics.push(ReplayBranchScalarClosureCandidateDiagnostic {
                branch_ordinal,
                initial_false_literals: initial_false,
                repair_kind: "no_repair".to_owned(),
                repair_changes: 0,
                raw_branch_false_literals: None,
                raw_total_false_conjuncts: None,
                closure_steps: Vec::new(),
                final_branch_false_literals: None,
                final_total_false_conjuncts: None,
                final_global_false_ordinal: None,
                final_global_false_term: None,
                final_global_false_eq: None,
            });
            continue;
        };

        let raw_branch_false = branch_false_literal_count(arena, branch, &trial)?;
        let raw_total_false = positive_replay_false_count(arena, originals, &trial)?;
        let (closure_steps, closure_trial) =
            replay_scalar_closure_from_trial(arena, originals, branch, &trial)?;
        let final_branch_false = branch_false_literal_count(arena, branch, &closure_trial)?;
        let final_total_false = positive_replay_false_count(arena, originals, &closure_trial)?;
        let final_failure = first_projected_replay_failure(
            arena,
            originals,
            &closure_trial,
            ProjectionRepairStats::default(),
        )?;
        diagnostics.push(ReplayBranchScalarClosureCandidateDiagnostic {
            branch_ordinal,
            initial_false_literals: initial_false,
            repair_kind,
            repair_changes,
            raw_branch_false_literals: Some(raw_branch_false),
            raw_total_false_conjuncts: Some(raw_total_false),
            closure_steps,
            final_branch_false_literals: Some(final_branch_false),
            final_total_false_conjuncts: Some(final_total_false),
            final_global_false_ordinal: final_failure
                .as_ref()
                .map(|failure| failure.conjunct_ordinal),
            final_global_false_term: final_failure.as_ref().map(|failure| failure.conjunct_term),
            final_global_false_eq: final_failure
                .as_ref()
                .and_then(|failure| failure.failed_eq.clone()),
        });
    }

    diagnostics.sort_by_key(|diagnostic| {
        (
            diagnostic.final_total_false_conjuncts.unwrap_or(usize::MAX),
            diagnostic.final_branch_false_literals.unwrap_or(usize::MAX),
            diagnostic.initial_false_literals,
            diagnostic.branch_ordinal,
        )
    });
    diagnostics.truncate(MAX_SCALAR_CLOSURE_REPORTED_BRANCHES);
    Ok(diagnostics)
}

fn enrich_replay_or_failure_with_scalar_choices(
    arena: &TermArena,
    originals: &[TermId],
    assignment: &Assignment,
    disjunction: TermId,
    mut or_failure: ReplayOrFailure,
) -> Result<ReplayOrFailure, SolverError> {
    for detail in &mut or_failure.best_branch_false_literal_details {
        detail.scalar_choices = replay_scalar_choice_diagnostics_for_literal(
            arena,
            originals,
            or_failure.best_branch_term,
            assignment,
            detail.literal_term,
        )?;
    }
    or_failure.scalar_closure_branch_candidates = replay_scalar_closure_branch_candidates(
        arena,
        originals,
        assignment,
        disjunction,
        &or_failure,
    )?;
    or_failure.best_branch_paired_scalar_chain =
        replay_paired_scalar_chain_diagnostic_for_or_failure(
            arena,
            originals,
            assignment,
            &or_failure,
        )?;
    Ok(or_failure)
}

#[derive(Clone, Copy)]
enum IntOrderRelation {
    Lt,
    Le,
    Gt,
    Ge,
}

impl IntOrderRelation {
    fn negated(self) -> Self {
        match self {
            Self::Lt => Self::Ge,
            Self::Le => Self::Gt,
            Self::Gt => Self::Le,
            Self::Ge => Self::Lt,
        }
    }
}

fn int_order_goal(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, IntOrderRelation)> {
    match arena.node(term) {
        TermNode::App { op, args } => match op {
            Op::IntLt => Some((args[0], args[1], IntOrderRelation::Lt)),
            Op::IntLe => Some((args[0], args[1], IntOrderRelation::Le)),
            Op::IntGt => Some((args[0], args[1], IntOrderRelation::Gt)),
            Op::IntGe => Some((args[0], args[1], IntOrderRelation::Ge)),
            Op::BoolNot => {
                let (lhs, rhs, relation) = int_order_goal(arena, args[0])?;
                Some((lhs, rhs, relation.negated()))
            }
            _ => None,
        },
        _ => None,
    }
}

fn direct_int_symbol(arena: &TermArena, term: TermId) -> Option<SymbolId> {
    let symbol = direct_value_symbol(arena, term)?;
    (arena.symbol(symbol).1 == Sort::Int).then_some(symbol)
}

fn int_order_left_value(relation: IntOrderRelation, rhs: i128) -> Option<i128> {
    match relation {
        IntOrderRelation::Lt => rhs.checked_sub(1),
        IntOrderRelation::Le | IntOrderRelation::Ge => Some(rhs),
        IntOrderRelation::Gt => rhs.checked_add(1),
    }
}

fn int_order_right_value(relation: IntOrderRelation, lhs: i128) -> Option<i128> {
    match relation {
        IntOrderRelation::Lt => lhs.checked_add(1),
        IntOrderRelation::Le | IntOrderRelation::Ge => Some(lhs),
        IntOrderRelation::Gt => lhs.checked_sub(1),
    }
}

fn int_order_repair_choices(
    arena: &TermArena,
    term: TermId,
    projected: &Assignment,
) -> Result<Vec<(SymbolId, Value)>, SolverError> {
    let Some((lhs_term, rhs_term, relation)) = int_order_goal(arena, term) else {
        return Ok(Vec::new());
    };
    let ir =
        |e: axeyum_ir::IrError| SolverError::Backend(format!("lazy-ext order repair failed: {e}"));
    let lhs = eval(arena, lhs_term, projected).map_err(ir)?;
    let rhs = eval(arena, rhs_term, projected).map_err(ir)?;
    let (Value::Int(lhs_value), Value::Int(rhs_value)) = (lhs, rhs) else {
        return Ok(Vec::new());
    };

    let mut choices = Vec::new();
    if let Some(symbol) = direct_int_symbol(arena, lhs_term)
        && let Some(value) = int_order_left_value(relation, rhs_value)
    {
        choices.push((symbol, Value::Int(value)));
    }
    if let Some(symbol) = direct_int_symbol(arena, rhs_term)
        && let Some(value) = int_order_right_value(relation, lhs_value)
        && !choices.iter().any(|(existing, existing_value)| {
            *existing == symbol && *existing_value == Value::Int(value)
        })
    {
        choices.push((symbol, Value::Int(value)));
    }
    Ok(choices)
}

fn store_projected_symbol_value(
    arena: &TermArena,
    projected: &mut Assignment,
    symbol: SymbolId,
    value: Value,
) -> Result<bool, SolverError> {
    let expected = arena.symbol(symbol).1;
    if value.sort() != expected {
        return Err(SolverError::Backend(format!(
            "branch repair sort mismatch for symbol #{}: expected {expected}, got {}",
            symbol.index(),
            value.sort()
        )));
    }
    if projected.get(symbol) == Some(value.clone()) {
        return Ok(false);
    }
    projected.set(symbol, value);
    Ok(true)
}

fn store_value(value: &Value, index: Value, element: Value) -> Result<Value, SolverError> {
    match value {
        Value::Array(array) => {
            let (_, index_value) = index.as_bv().ok_or_else(|| {
                SolverError::Backend("store repair expected a bit-vector index".to_owned())
            })?;
            let (_, element_value) = element.as_bv().ok_or_else(|| {
                SolverError::Backend("store repair expected a bit-vector element".to_owned())
            })?;
            Ok(Value::Array(array.store(index_value, element_value)))
        }
        Value::GenericArray(array) => Ok(Value::GenericArray(array.store(index, element))),
        other => Err(SolverError::Backend(format!(
            "store repair expected an array value, got {other}"
        ))),
    }
}

fn select_value(value: &Value, index: &Value) -> Result<Value, SolverError> {
    match value {
        Value::Array(array) => {
            let (_, index_value) = index.as_bv().ok_or_else(|| {
                SolverError::Backend("store repair expected a bit-vector index".to_owned())
            })?;
            Ok(Value::Bv {
                width: array.element_width(),
                value: array.select(index_value),
            })
        }
        Value::GenericArray(array) => Ok(array.select(index)),
        other => Err(SolverError::Backend(format!(
            "store repair expected an array value, got {other}"
        ))),
    }
}

fn default_value_for_symbol(arena: &TermArena, symbol: SymbolId) -> Result<Value, SolverError> {
    let sort = arena.symbol(symbol).1;
    well_founded_default(arena, sort).ok_or_else(|| {
        SolverError::Backend(format!(
            "store repair could not construct default for symbol #{}",
            symbol.index()
        ))
    })
}

#[derive(Clone, Copy)]
struct StoreBaseRepairTarget {
    target_symbol: SymbolId,
    base_symbol: SymbolId,
    target_array: TermId,
    index_term: TermId,
    element_term: TermId,
}

fn store_base_repair_target(arena: &TermArena, term: TermId) -> Option<StoreBaseRepairTarget> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    store_base_repair_side(arena, args[0], args[1])
        .or_else(|| store_base_repair_side(arena, args[1], args[0]))
}

fn store_base_repair_side(
    arena: &TermArena,
    target_array: TermId,
    store_term: TermId,
) -> Option<StoreBaseRepairTarget> {
    direct_array_symbol(arena, target_array).and_then(|target| {
        let TermNode::App {
            op: Op::Store,
            args,
        } = arena.node(store_term)
        else {
            return None;
        };
        let base = direct_array_symbol(arena, args[0])?;
        Some(StoreBaseRepairTarget {
            target_symbol: target,
            base_symbol: base,
            target_array,
            index_term: args[1],
            element_term: args[2],
        })
    })
}

#[derive(Clone, Copy)]
enum SelectedArrayDefinition {
    Store(StoreBaseRepairTarget),
    Equal(SymbolId),
}

fn selected_array_definitions_for_symbol(
    arena: &TermArena,
    originals: &[TermId],
    projected: &Assignment,
    array_symbol: SymbolId,
) -> Result<Vec<SelectedArrayDefinition>, SolverError> {
    let mut definitions = Vec::new();
    let mut conjuncts = Vec::new();
    let mut literals = Vec::new();
    for &assertion in originals {
        conjuncts.clear();
        collect_positive_conjuncts(arena, assertion, &mut conjuncts);
        for &conjunct in &conjuncts {
            let selected_branch =
                if matches!(arena.node(conjunct), TermNode::App { op: Op::BoolOr, .. }) {
                    let Some(or_failure) = replay_failed_or_details(arena, conjunct, projected)?
                    else {
                        continue;
                    };
                    if or_failure.best_branch_false_literals > 1 {
                        continue;
                    }
                    or_failure.best_branch_term
                } else {
                    conjunct
                };
            literals.clear();
            collect_positive_conjuncts(arena, selected_branch, &mut literals);
            for &literal in &literals {
                if let Some(target) = store_base_repair_target(arena, literal) {
                    if target.target_symbol == array_symbol {
                        definitions.push(SelectedArrayDefinition::Store(target));
                    }
                    continue;
                }
                let Some((lhs, rhs)) = direct_array_equality_repair_target(arena, literal) else {
                    continue;
                };
                if lhs == array_symbol {
                    definitions.push(SelectedArrayDefinition::Equal(rhs));
                } else if rhs == array_symbol {
                    definitions.push(SelectedArrayDefinition::Equal(lhs));
                }
            }
        }
    }
    Ok(definitions)
}

#[allow(clippy::too_many_arguments)]
fn repair_projected_store_chain_readback(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
    array_symbol: SymbolId,
    read_index: &Value,
    read_element: &Value,
    depth: usize,
    visited: &mut BTreeSet<SymbolId>,
    stats: &mut ProjectionRepairStats,
) -> Result<bool, SolverError> {
    const MAX_STORE_CHAIN_READBACK_DEPTH: usize = 8;

    if depth > MAX_STORE_CHAIN_READBACK_DEPTH || !visited.insert(array_symbol) {
        return Ok(false);
    }

    let array_value = projected
        .get(array_symbol)
        .unwrap_or(default_value_for_symbol(arena, array_symbol)?);
    if select_value(&array_value, read_index)? == *read_element {
        visited.remove(&array_symbol);
        return Ok(false);
    }

    let definitions =
        selected_array_definitions_for_symbol(arena, originals, projected, array_symbol)?;
    for definition in definitions {
        let before = projected.clone();
        let before_stats = *stats;
        let changed = match definition {
            SelectedArrayDefinition::Store(target) => repair_projected_store_definition_readback(
                arena,
                originals,
                projected,
                target,
                read_index,
                read_element,
                depth,
                visited,
                stats,
            )?,
            SelectedArrayDefinition::Equal(other_symbol) => {
                let other_changed = repair_projected_store_chain_readback(
                    arena,
                    originals,
                    projected,
                    other_symbol,
                    read_index,
                    read_element,
                    depth + 1,
                    visited,
                    stats,
                )?;
                let other_value = projected
                    .get(other_symbol)
                    .unwrap_or(default_value_for_symbol(arena, other_symbol)?);
                let mut changed = other_changed;
                if store_projected_symbol_value(arena, projected, array_symbol, other_value)? {
                    stats.branch_symbol_changes += 1;
                    changed = true;
                }
                let readback_changes = align_direct_select_symbols_for_array(
                    arena,
                    originals,
                    projected,
                    array_symbol,
                )?;
                stats.symbol_changes += readback_changes;
                changed || readback_changes > 0
            }
        };

        let repaired_value = projected
            .get(array_symbol)
            .unwrap_or(default_value_for_symbol(arena, array_symbol)?);
        if changed && select_value(&repaired_value, read_index)? == *read_element {
            visited.remove(&array_symbol);
            return Ok(true);
        }

        *projected = before;
        *stats = before_stats;
    }

    if store_projected_array_entry(
        arena,
        projected,
        array_symbol,
        read_index.clone(),
        read_element.clone(),
    )? {
        stats.array_changes += 1;
        let readback_changes =
            align_direct_select_symbols_for_array(arena, originals, projected, array_symbol)?;
        stats.symbol_changes += readback_changes;
        visited.remove(&array_symbol);
        return Ok(true);
    }

    visited.remove(&array_symbol);
    Ok(false)
}

#[allow(clippy::too_many_arguments)]
fn repair_projected_store_definition_readback(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
    target: StoreBaseRepairTarget,
    read_index: &Value,
    read_element: &Value,
    depth: usize,
    visited: &mut BTreeSet<SymbolId>,
    stats: &mut ProjectionRepairStats,
) -> Result<bool, SolverError> {
    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext store-chain readback repair failed: {e}"))
    };
    stats.branch_candidates += 1;
    let store_index = eval(arena, target.index_term, projected).map_err(ir)?;
    let mut store_element = eval(arena, target.element_term, projected).map_err(ir)?;
    let mut changed = false;

    if store_index == *read_index {
        if store_element != *read_element {
            let Some(element_symbol) = direct_value_symbol(arena, target.element_term) else {
                return Ok(false);
            };
            if store_projected_symbol_value(arena, projected, element_symbol, read_element.clone())?
            {
                stats.branch_symbol_changes += 1;
                changed = true;
            }
            store_element = read_element.clone();
        }
    } else {
        let base_changed = repair_projected_store_chain_readback(
            arena,
            originals,
            projected,
            target.base_symbol,
            read_index,
            read_element,
            depth + 1,
            visited,
            stats,
        )?;
        changed |= base_changed;
    }

    let base_value = projected
        .get(target.base_symbol)
        .unwrap_or(default_value_for_symbol(arena, target.base_symbol)?);
    let repaired_target = store_value(&base_value, store_index, store_element)?;
    if store_projected_symbol_value(arena, projected, target.target_symbol, repaired_target)? {
        stats.branch_symbol_changes += 1;
        changed = true;
    }
    let base_readback_changes =
        align_direct_select_symbols_for_array(arena, originals, projected, target.base_symbol)?;
    let target_readback_changes =
        align_direct_select_symbols_for_array(arena, originals, projected, target.target_symbol)?;
    stats.symbol_changes += base_readback_changes + target_readback_changes;
    Ok(changed || base_readback_changes > 0 || target_readback_changes > 0)
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn repair_projected_array_symbol_to_value_through_definitions(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
    array_symbol: SymbolId,
    desired_value: &Value,
    depth: usize,
    visited: &mut BTreeSet<SymbolId>,
    stats: &mut ProjectionRepairStats,
) -> Result<bool, SolverError> {
    const MAX_ARRAY_VALUE_REPAIR_DEPTH: usize = 8;

    if depth > MAX_ARRAY_VALUE_REPAIR_DEPTH || !visited.insert(array_symbol) {
        return Ok(false);
    }

    let result = (|| -> Result<bool, SolverError> {
        let current = projected
            .get(array_symbol)
            .unwrap_or(default_value_for_symbol(arena, array_symbol)?);
        if current == *desired_value {
            return Ok(false);
        }

        let mut best: Option<(usize, usize, ProjectionRepairStats, Assignment)> = None;
        let definitions =
            selected_array_definitions_for_symbol(arena, originals, projected, array_symbol)?;
        for (ordinal, definition) in definitions.into_iter().enumerate() {
            let mut trial = projected.clone();
            let mut trial_stats = ProjectionRepairStats::default();
            let changed = match definition {
                SelectedArrayDefinition::Store(target) => {
                    repair_projected_store_definition_to_value(
                        arena,
                        originals,
                        &mut trial,
                        target,
                        desired_value,
                        depth,
                        visited,
                        &mut trial_stats,
                    )?
                }
                SelectedArrayDefinition::Equal(other_symbol) => {
                    let other_changed = repair_projected_array_symbol_to_value_through_definitions(
                        arena,
                        originals,
                        &mut trial,
                        other_symbol,
                        desired_value,
                        depth + 1,
                        visited,
                        &mut trial_stats,
                    )?;
                    let other_value = trial
                        .get(other_symbol)
                        .unwrap_or(default_value_for_symbol(arena, other_symbol)?);
                    let mut changed = other_changed;
                    if store_projected_symbol_value(arena, &mut trial, array_symbol, other_value)? {
                        trial_stats.branch_symbol_changes += 1;
                        changed = true;
                    }
                    let readback_changes = align_direct_select_symbols_for_array(
                        arena,
                        originals,
                        &mut trial,
                        array_symbol,
                    )?;
                    trial_stats.symbol_changes += readback_changes;
                    changed || readback_changes > 0
                }
            };
            let repaired_value = trial
                .get(array_symbol)
                .unwrap_or(default_value_for_symbol(arena, array_symbol)?);
            if !changed || repaired_value != *desired_value {
                continue;
            }
            let total_false = positive_replay_false_count(arena, originals, &trial)?;
            let replace = best
                .as_ref()
                .is_none_or(|(best_total_false, best_ordinal, _, _)| {
                    (total_false, ordinal) < (*best_total_false, *best_ordinal)
                });
            if replace {
                best = Some((total_false, ordinal, trial_stats, trial));
            }
        }

        if best.is_none() {
            let mut trial = projected.clone();
            let mut trial_stats = ProjectionRepairStats::default();
            if store_projected_symbol_value(arena, &mut trial, array_symbol, desired_value.clone())?
            {
                trial_stats.branch_symbol_changes += 1;
                let readback_changes = align_direct_select_symbols_for_array(
                    arena,
                    originals,
                    &mut trial,
                    array_symbol,
                )?;
                trial_stats.symbol_changes += readback_changes;
                let total_false = positive_replay_false_count(arena, originals, &trial)?;
                best = Some((total_false, usize::MAX, trial_stats, trial));
            }
        }

        let Some((_, _, best_stats, trial)) = best else {
            return Ok(false);
        };
        *projected = trial;
        stats.absorb(best_stats);
        Ok(true)
    })();

    visited.remove(&array_symbol);
    result
}

#[allow(clippy::too_many_arguments)]
fn repair_projected_store_definition_to_value(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
    target: StoreBaseRepairTarget,
    desired_value: &Value,
    depth: usize,
    visited: &mut BTreeSet<SymbolId>,
    stats: &mut ProjectionRepairStats,
) -> Result<bool, SolverError> {
    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext store-chain equality repair failed: {e}"))
    };
    stats.branch_candidates += 1;
    let store_index = eval(arena, target.index_term, projected).map_err(ir)?;
    let mut store_element = eval(arena, target.element_term, projected).map_err(ir)?;
    let desired_store_cell = select_value(desired_value, &store_index)?;
    let mut changed = false;

    if store_element != desired_store_cell {
        let Some(element_symbol) = direct_value_symbol(arena, target.element_term) else {
            return Ok(false);
        };
        if store_projected_symbol_value(
            arena,
            projected,
            element_symbol,
            desired_store_cell.clone(),
        )? {
            stats.branch_symbol_changes += 1;
            changed = true;
        }
        store_element = desired_store_cell;
    }

    let current_base = projected
        .get(target.base_symbol)
        .unwrap_or(default_value_for_symbol(arena, target.base_symbol)?);
    let preserved_base_cell = select_value(&current_base, &store_index)?;
    let desired_base = store_value(desired_value, store_index.clone(), preserved_base_cell)?;
    let base_changed = repair_projected_array_symbol_to_value_through_definitions(
        arena,
        originals,
        projected,
        target.base_symbol,
        &desired_base,
        depth + 1,
        visited,
        stats,
    )?;
    changed |= base_changed;

    let repaired_base = projected
        .get(target.base_symbol)
        .unwrap_or(default_value_for_symbol(arena, target.base_symbol)?);
    let repaired_target = store_value(&repaired_base, store_index, store_element)?;
    if repaired_target != *desired_value {
        return Ok(false);
    }
    if store_projected_symbol_value(arena, projected, target.target_symbol, repaired_target)? {
        stats.branch_symbol_changes += 1;
        changed = true;
    }
    let base_readback_changes =
        align_direct_select_symbols_for_array(arena, originals, projected, target.base_symbol)?;
    let target_readback_changes =
        align_direct_select_symbols_for_array(arena, originals, projected, target.target_symbol)?;
    stats.symbol_changes += base_readback_changes + target_readback_changes;
    Ok(changed || base_readback_changes > 0 || target_readback_changes > 0)
}

fn branch_false_literal_count(
    arena: &TermArena,
    branch: TermId,
    assignment: &Assignment,
) -> Result<usize, SolverError> {
    let mut literals = Vec::new();
    collect_positive_conjuncts(arena, branch, &mut literals);
    let mut false_literals = 0;
    for literal in literals {
        match eval(arena, literal, assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => false_literals += 1,
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "lazy-ext branch repair: literal #{} evaluated to non-Boolean {value}",
                    literal.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "lazy-ext branch repair: literal #{} failed evaluation: {error}",
                    literal.index()
                )));
            }
        }
    }
    Ok(false_literals)
}

fn positive_replay_false_count(
    arena: &TermArena,
    originals: &[TermId],
    assignment: &Assignment,
) -> Result<usize, SolverError> {
    let mut false_conjuncts = 0;
    let mut conjuncts = Vec::new();
    for &assertion in originals {
        conjuncts.clear();
        collect_positive_conjuncts(arena, assertion, &mut conjuncts);
        for &conjunct in &conjuncts {
            match eval(arena, conjunct, assignment) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => false_conjuncts += 1,
                Ok(value) => {
                    return Err(SolverError::Backend(format!(
                        "lazy-ext scalar repair: conjunct #{} evaluated to non-Boolean {value}",
                        conjunct.index()
                    )));
                }
                Err(error) => {
                    return Err(SolverError::Backend(format!(
                        "lazy-ext scalar repair: conjunct #{} failed evaluation: {error}",
                        conjunct.index()
                    )));
                }
            }
        }
    }
    Ok(false_conjuncts)
}

fn repair_projected_store_base_literal(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
    target: StoreBaseRepairTarget,
    align_target_readbacks: bool,
    stats: &mut ProjectionRepairStats,
) -> Result<bool, SolverError> {
    let ir =
        |e: axeyum_ir::IrError| SolverError::Backend(format!("lazy-ext branch repair failed: {e}"));
    let target_value = eval(arena, target.target_array, projected).map_err(ir)?;
    let index = eval(arena, target.index_term, projected).map_err(ir)?;
    let element = eval(arena, target.element_term, projected).map_err(ir)?;
    stats.branch_candidates += 1;
    let mut changed = false;
    if store_value(&target_value, index.clone(), element.clone())? == target_value {
        let current_base = projected
            .get(target.base_symbol)
            .unwrap_or(default_value_for_symbol(arena, target.base_symbol)?);
        let current_store_cell = select_value(&current_base, &index)?;
        let repaired_base = store_value(&target_value, index, current_store_cell)?;
        if store_projected_symbol_value(arena, projected, target.base_symbol, repaired_base)? {
            stats.branch_symbol_changes += 1;
            changed = true;
        }
        let readback_changes =
            align_direct_select_symbols_for_array(arena, originals, projected, target.base_symbol)?;
        stats.symbol_changes += readback_changes;
        return Ok(changed || readback_changes > 0);
    }

    let current_base = projected
        .get(target.base_symbol)
        .unwrap_or(default_value_for_symbol(arena, target.base_symbol)?);
    let repaired_target = store_value(&current_base, index, element)?;
    if store_projected_symbol_value(arena, projected, target.target_symbol, repaired_target)? {
        stats.branch_symbol_changes += 1;
        changed = true;
    }
    let readback_changes = if align_target_readbacks {
        align_direct_select_symbols_for_array(arena, originals, projected, target.target_symbol)?
    } else {
        0
    };
    stats.symbol_changes += readback_changes;
    Ok(changed || readback_changes > 0)
}

fn repair_projected_store_target_from_current_base(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
    target: StoreBaseRepairTarget,
    stats: &mut ProjectionRepairStats,
) -> Result<bool, SolverError> {
    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext branch residual repair failed: {e}"))
    };
    let index = eval(arena, target.index_term, projected).map_err(ir)?;
    let element = eval(arena, target.element_term, projected).map_err(ir)?;
    let current_base = projected
        .get(target.base_symbol)
        .unwrap_or(default_value_for_symbol(arena, target.base_symbol)?);
    let repaired_target = store_value(&current_base, index, element)?;
    stats.branch_candidates += 1;
    let mut changed = false;
    if store_projected_symbol_value(arena, projected, target.target_symbol, repaired_target)? {
        stats.branch_symbol_changes += 1;
        changed = true;
    }
    let readback_changes =
        align_direct_select_symbols_for_array(arena, originals, projected, target.target_symbol)?;
    stats.symbol_changes += readback_changes;
    Ok(changed || readback_changes > 0)
}

fn repair_projected_array_equality_literal(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
    lhs_symbol: SymbolId,
    rhs_symbol: SymbolId,
    stats: &mut ProjectionRepairStats,
) -> Result<bool, SolverError> {
    let lhs_value = projected
        .get(lhs_symbol)
        .unwrap_or(default_value_for_symbol(arena, lhs_symbol)?);
    let rhs_value = projected
        .get(rhs_symbol)
        .unwrap_or(default_value_for_symbol(arena, rhs_symbol)?);
    if lhs_value == rhs_value {
        return Ok(false);
    }
    let lhs_key = array_equality_repair_key(arena, originals, projected, lhs_symbol, &lhs_value)?;
    let rhs_key = array_equality_repair_key(arena, originals, projected, rhs_symbol, &rhs_value)?;
    let repair = match lhs_key.cmp(&rhs_key) {
        std::cmp::Ordering::Greater => Some((rhs_symbol, lhs_value)),
        std::cmp::Ordering::Less => Some((lhs_symbol, rhs_value)),
        std::cmp::Ordering::Equal => None,
    };
    let Some((target_symbol, value)) = repair else {
        return Ok(false);
    };
    stats.branch_candidates += 1;
    let mut changed = false;
    if store_projected_symbol_value(arena, projected, target_symbol, value)? {
        stats.branch_symbol_changes += 1;
        changed = true;
    }
    let readback_changes =
        align_direct_select_symbols_for_array(arena, originals, projected, target_symbol)?;
    stats.symbol_changes += readback_changes;
    Ok(changed || readback_changes > 0)
}

fn selected_array_equality_component(
    arena: &TermArena,
    originals: &[TermId],
    projected: &Assignment,
    lhs_symbol: SymbolId,
    rhs_symbol: SymbolId,
) -> Result<BTreeSet<SymbolId>, SolverError> {
    let mut component = BTreeSet::from([lhs_symbol, rhs_symbol]);
    let mut conjuncts = Vec::new();
    let mut literals = Vec::new();
    loop {
        let before = component.len();
        for &assertion in originals {
            conjuncts.clear();
            collect_positive_conjuncts(arena, assertion, &mut conjuncts);
            for &conjunct in &conjuncts {
                let selected_branch =
                    if matches!(arena.node(conjunct), TermNode::App { op: Op::BoolOr, .. }) {
                        let Some(or_failure) =
                            replay_failed_or_details(arena, conjunct, projected)?
                        else {
                            continue;
                        };
                        if or_failure.best_branch_false_literals > 1 {
                            continue;
                        }
                        or_failure.best_branch_term
                    } else {
                        conjunct
                    };
                literals.clear();
                collect_positive_conjuncts(arena, selected_branch, &mut literals);
                for &literal in &literals {
                    let Some((lhs, rhs)) = direct_array_equality_repair_target(arena, literal)
                    else {
                        continue;
                    };
                    if component.contains(&lhs) || component.contains(&rhs) {
                        component.insert(lhs);
                        component.insert(rhs);
                    }
                }
            }
        }
        if component.len() == before {
            break;
        }
    }
    Ok(component)
}

#[allow(clippy::too_many_lines)]
fn repair_projected_array_equality_component_literal(
    arena: &TermArena,
    originals: &[TermId],
    branch: TermId,
    projected: &mut Assignment,
    lhs_symbol: SymbolId,
    rhs_symbol: SymbolId,
    stats: &mut ProjectionRepairStats,
) -> Result<bool, SolverError> {
    let current_total_false = positive_replay_false_count(arena, originals, projected)?;
    let current_branch_false = branch_false_literal_count(arena, branch, projected)?;
    if current_branch_false == 0 {
        return Ok(false);
    }

    let component =
        selected_array_equality_component(arena, originals, projected, lhs_symbol, rhs_symbol)?;
    let mut best: Option<(usize, usize, usize, ProjectionRepairStats, Assignment)> = None;
    let mut consider = |ordinal: usize,
                        trial_stats: ProjectionRepairStats,
                        trial: Assignment,
                        changed: bool|
     -> Result<(), SolverError> {
        if !changed {
            return Ok(());
        }

        let branch_false = branch_false_literal_count(arena, branch, &trial)?;
        if branch_false >= current_branch_false {
            return Ok(());
        }
        let total_false = positive_replay_false_count(arena, originals, &trial)?;
        if total_false > current_total_false {
            return Ok(());
        }
        let replace = best.as_ref().is_none_or(
            |(best_total_false, best_branch_false, best_ordinal, _, _)| {
                (total_false, branch_false, ordinal)
                    < (*best_total_false, *best_branch_false, *best_ordinal)
            },
        );
        if replace {
            best = Some((total_false, branch_false, ordinal, trial_stats, trial));
        }
        Ok(())
    };

    for (ordinal, &source_symbol) in component.iter().enumerate() {
        let source_value = projected
            .get(source_symbol)
            .unwrap_or(default_value_for_symbol(arena, source_symbol)?);
        let mut trial = projected.clone();
        let mut trial_stats = ProjectionRepairStats {
            branch_candidates: 1,
            ..ProjectionRepairStats::default()
        };
        let mut changed = false;
        for &target_symbol in &component {
            if store_projected_symbol_value(arena, &mut trial, target_symbol, source_value.clone())?
            {
                trial_stats.branch_symbol_changes += 1;
                changed = true;
            }
        }
        for &target_symbol in &component {
            let readback_changes =
                align_direct_select_symbols_for_array(arena, originals, &mut trial, target_symbol)?;
            trial_stats.symbol_changes += readback_changes;
            changed |= readback_changes > 0;
        }
        consider(ordinal, trial_stats, trial, changed)?;
    }

    let definition_ordinal_base = component.len();
    for (source_ordinal, &source_symbol) in component.iter().enumerate() {
        let source_value = projected
            .get(source_symbol)
            .unwrap_or(default_value_for_symbol(arena, source_symbol)?);
        let mut trial = projected.clone();
        let mut trial_stats = ProjectionRepairStats {
            branch_candidates: 1,
            ..ProjectionRepairStats::default()
        };
        let mut changed = false;
        for &target_symbol in &component {
            let mut visited = BTreeSet::new();
            if repair_projected_array_symbol_to_value_through_definitions(
                arena,
                originals,
                &mut trial,
                target_symbol,
                &source_value,
                0,
                &mut visited,
                &mut trial_stats,
            )? {
                changed = true;
            }
        }
        for &target_symbol in &component {
            let readback_changes =
                align_direct_select_symbols_for_array(arena, originals, &mut trial, target_symbol)?;
            trial_stats.symbol_changes += readback_changes;
            changed |= readback_changes > 0;
        }
        consider(
            definition_ordinal_base + source_ordinal,
            trial_stats,
            trial,
            changed,
        )?;
    }

    let Some((_, _, _, best_stats, trial)) = best else {
        return Ok(false);
    };
    *projected = trial;
    stats.absorb(best_stats);
    Ok(true)
}

fn repair_projected_branch_literal_in_branch(
    arena: &TermArena,
    originals: &[TermId],
    branch: TermId,
    literal: TermId,
    projected: &mut Assignment,
    stats: &mut ProjectionRepairStats,
) -> Result<bool, SolverError> {
    if let Some((lhs_symbol, rhs_symbol)) = direct_array_equality_repair_target(arena, literal)
        && repair_projected_array_equality_component_literal(
            arena, originals, branch, projected, lhs_symbol, rhs_symbol, stats,
        )?
    {
        return Ok(true);
    }
    repair_projected_branch_literal(arena, originals, literal, projected, stats)
}

fn repair_projected_order_literal(
    arena: &TermArena,
    originals: &[TermId],
    literal: TermId,
    projected: &mut Assignment,
    stats: &mut ProjectionRepairStats,
) -> Result<bool, SolverError> {
    let choices = int_order_repair_choices(arena, literal, projected)?;
    if choices.is_empty() {
        return Ok(false);
    }
    let ir =
        |e: axeyum_ir::IrError| SolverError::Backend(format!("lazy-ext order repair failed: {e}"));
    let current_false = positive_replay_false_count(arena, originals, projected)?;
    let mut best: Option<(usize, usize, ProjectionRepairStats, Assignment)> = None;

    for (ordinal, (symbol, value)) in choices.into_iter().enumerate() {
        let mut trial = projected.clone();
        let mut trial_stats = ProjectionRepairStats {
            branch_candidates: 1,
            ..ProjectionRepairStats::default()
        };
        if !store_projected_symbol_value(arena, &mut trial, symbol, value)? {
            continue;
        }
        trial_stats.branch_symbol_changes += 1;
        if eval(arena, literal, &trial).map_err(ir)? != Value::Bool(true) {
            continue;
        }
        let total_false = positive_replay_false_count(arena, originals, &trial)?;
        if total_false > current_false {
            continue;
        }
        let replace = best
            .as_ref()
            .is_none_or(|(best_total_false, best_ordinal, _, _)| {
                (total_false, ordinal) < (*best_total_false, *best_ordinal)
            });
        if replace {
            best = Some((total_false, ordinal, trial_stats, trial));
        }
    }

    let Some((_, _, best_stats, trial)) = best else {
        return Ok(false);
    };
    *projected = trial;
    stats.absorb(best_stats);
    Ok(true)
}

fn repair_projected_branch_scalar_equality_literal(
    arena: &TermArena,
    literal: TermId,
    projected: &mut Assignment,
    stats: &mut ProjectionRepairStats,
) -> Result<bool, SolverError> {
    let choices = direct_scalar_equality_repair_choices(arena, literal);
    if choices.is_empty() {
        return Ok(false);
    }
    let ir =
        |e: axeyum_ir::IrError| SolverError::Backend(format!("lazy-ext branch repair failed: {e}"));
    for (symbol, value_term) in choices {
        let mut trial = projected.clone();
        let value = eval(arena, value_term, &trial).map_err(ir)?;
        if !store_projected_symbol_value(arena, &mut trial, symbol, value)? {
            continue;
        }
        if eval(arena, literal, &trial).map_err(ir)? != Value::Bool(true) {
            continue;
        }
        *projected = trial;
        stats.branch_candidates += 1;
        stats.branch_symbol_changes += 1;
        return Ok(true);
    }
    Ok(false)
}

fn repair_projected_branch_scalar_choice_candidate(
    arena: &TermArena,
    originals: &[TermId],
    branch: TermId,
    projected: &mut Assignment,
) -> Result<Option<ProjectionRepairStats>, SolverError> {
    const MAX_BRANCH_SCALAR_CHOICE_DEPTH: usize = 4;
    const MAX_BRANCH_SCALAR_CHOICE_STATES: usize = 16;

    let initial_branch_false = branch_false_literal_count(arena, branch, projected)?;
    if initial_branch_false == 0 || initial_branch_false > MAX_BRANCH_SCALAR_CHOICE_DEPTH {
        return Ok(None);
    }
    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext scalar branch choice repair failed: {e}"))
    };

    let mut sequence = 0usize;
    let mut frontier = vec![(
        initial_branch_false,
        positive_replay_false_count(arena, originals, projected)?,
        sequence,
        ProjectionRepairStats::default(),
        projected.clone(),
    )];
    sequence += 1;
    let mut best: Option<(usize, usize, ProjectionRepairStats, Assignment)> = None;

    while !frontier.is_empty() {
        frontier.sort_by_key(|(branch_false, total_false, state_sequence, _, _)| {
            (*branch_false, *total_false, *state_sequence)
        });
        let (_, _, _, state_stats, state_assignment) = frontier.remove(0);
        let branch_false = branch_false_literal_count(arena, branch, &state_assignment)?;
        if branch_false == 0 {
            let total_false = positive_replay_false_count(arena, originals, &state_assignment)?;
            let replace = best
                .as_ref()
                .is_none_or(|(best_total_false, best_changes, _, _)| {
                    (total_false, state_stats.changes()) < (*best_total_false, *best_changes)
                });
            if replace {
                best = Some((
                    total_false,
                    state_stats.changes(),
                    state_stats,
                    state_assignment,
                ));
            }
            continue;
        }
        if state_stats.branch_symbol_changes >= MAX_BRANCH_SCALAR_CHOICE_DEPTH {
            continue;
        }

        let Some(false_literal) = branch_first_false_literal(arena, branch, &state_assignment)?
        else {
            continue;
        };
        let choices = direct_scalar_equality_repair_choices(arena, false_literal);
        if choices.is_empty() {
            continue;
        }
        for (symbol, value_term) in choices {
            let mut trial = state_assignment.clone();
            let value = eval(arena, value_term, &trial).map_err(ir)?;
            if !store_projected_symbol_value(arena, &mut trial, symbol, value)? {
                continue;
            }
            if eval(arena, false_literal, &trial).map_err(ir)? != Value::Bool(true) {
                continue;
            }
            let trial_branch_false = branch_false_literal_count(arena, branch, &trial)?;
            if trial_branch_false >= branch_false {
                continue;
            }
            let trial_total_false = positive_replay_false_count(arena, originals, &trial)?;
            let mut trial_stats = state_stats;
            trial_stats.branch_candidates += 1;
            trial_stats.branch_symbol_changes += 1;
            frontier.push((
                trial_branch_false,
                trial_total_false,
                sequence,
                trial_stats,
                trial,
            ));
            sequence += 1;
        }
        frontier.sort_by_key(|(branch_false, total_false, state_sequence, _, _)| {
            (*branch_false, *total_false, *state_sequence)
        });
        frontier.truncate(MAX_BRANCH_SCALAR_CHOICE_STATES);
    }

    let Some((_, _, stats, trial)) = best else {
        return Ok(None);
    };
    *projected = trial;
    Ok(Some(stats))
}

fn repair_projected_branch_literal(
    arena: &TermArena,
    originals: &[TermId],
    literal: TermId,
    projected: &mut Assignment,
    stats: &mut ProjectionRepairStats,
) -> Result<bool, SolverError> {
    let ir =
        |e: axeyum_ir::IrError| SolverError::Backend(format!("lazy-ext branch repair failed: {e}"));
    if let Some(target) = store_base_repair_target(arena, literal) {
        return repair_projected_store_base_literal(
            arena, originals, projected, target, true, stats,
        );
    }
    if let Some((lhs_symbol, rhs_symbol)) = direct_array_equality_repair_target(arena, literal) {
        return repair_projected_array_equality_literal(
            arena, originals, projected, lhs_symbol, rhs_symbol, stats,
        );
    }
    if repair_projected_order_literal(arena, originals, literal, projected, stats)? {
        return Ok(true);
    }
    let Some((symbol, value_term)) = direct_symbol_equality_repair_target(arena, literal) else {
        return Ok(false);
    };
    stats.branch_candidates += 1;
    let value = eval(arena, value_term, projected).map_err(ir)?;
    if store_projected_symbol_value(arena, projected, symbol, value)? {
        stats.branch_symbol_changes += 1;
        return Ok(true);
    }
    Ok(false)
}

fn repair_projected_branch_schedule(
    arena: &TermArena,
    originals: &[TermId],
    branch: TermId,
    projected: &mut Assignment,
) -> Result<Option<ProjectionRepairStats>, SolverError> {
    let ir =
        |e: axeyum_ir::IrError| SolverError::Backend(format!("lazy-ext branch repair failed: {e}"));
    let initial_false = branch_false_literal_count(arena, branch, projected)?;
    if !(2..=8).contains(&initial_false) {
        return Ok(None);
    }

    let mut trial = projected.clone();
    let mut stats = ProjectionRepairStats::default();
    let mut changed = false;
    let mut literals = Vec::new();
    collect_positive_conjuncts(arena, branch, &mut literals);

    for _ in 0..=2 {
        let mut pass_changes = 0;
        for &literal in &literals {
            if eval(arena, literal, &trial).map_err(ir)? == Value::Bool(true) {
                continue;
            }
            let Some((symbol, value_term)) = direct_scalar_equality_repair_target(arena, literal)
            else {
                continue;
            };
            stats.branch_candidates += 1;
            let value = eval(arena, value_term, &trial).map_err(ir)?;
            if store_projected_symbol_value(arena, &mut trial, symbol, value)? {
                stats.branch_symbol_changes += 1;
                pass_changes += 1;
                changed = true;
            }
        }
        if pass_changes == 0 {
            break;
        }
    }

    for &literal in &literals {
        if eval(arena, literal, &trial).map_err(ir)? == Value::Bool(true) {
            continue;
        }
        if repair_projected_branch_literal(arena, originals, literal, &mut trial, &mut stats)? {
            changed = true;
        }
    }

    let final_false = branch_false_literal_count(arena, branch, &trial)?;
    if changed && final_false < initial_false {
        *projected = trial;
        Ok(Some(stats))
    } else {
        Ok(None)
    }
}

fn repair_projected_scalar_equalities(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
) -> Result<ProjectionRepairStats, SolverError> {
    const MAX_SCALAR_EQUALITY_REPAIRS: usize = 64;

    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext scalar equality repair failed: {e}"))
    };
    let mut stats = ProjectionRepairStats::default();
    let mut current_false = positive_replay_false_count(arena, originals, projected)?;
    if current_false == 0 {
        return Ok(stats);
    }

    let mut repairs = 0;
    for _ in 0..=2 {
        let mut changed_this_pass = false;
        let mut conjuncts = Vec::new();
        for &assertion in originals {
            conjuncts.clear();
            collect_positive_conjuncts(arena, assertion, &mut conjuncts);
            for &conjunct in &conjuncts {
                if repairs >= MAX_SCALAR_EQUALITY_REPAIRS || current_false == 0 {
                    return Ok(stats);
                }
                if eval(arena, conjunct, projected).map_err(ir)? != Value::Bool(false) {
                    continue;
                }
                let choices = direct_scalar_equality_repair_choices(arena, conjunct);
                if choices.is_empty() {
                    continue;
                }
                stats.scalar_candidates += 1;

                let mut best: Option<(usize, usize, Assignment, ProjectionRepairStats)> = None;
                for (symbol, value_term) in choices {
                    let mut trial = projected.clone();
                    let value = eval(arena, value_term, &trial).map_err(ir)?;
                    if !store_projected_symbol_value(arena, &mut trial, symbol, value)? {
                        continue;
                    }
                    let target_support =
                        scalar_select_support_score(arena, originals, projected, symbol)?;
                    let source_support = direct_value_symbol(arena, value_term)
                        .map_or(Ok(0), |source| {
                            scalar_select_support_score(arena, originals, projected, source)
                        })?;
                    let support_gain = source_support.saturating_sub(target_support);
                    if support_gain > 0 {
                        stats.scalar_support_candidates += 1;
                    }
                    let mut trial_stats = ProjectionRepairStats::default();
                    let mut false_count = positive_replay_false_count(arena, originals, &trial)?;
                    if false_count >= current_false && support_gain > 0 {
                        stats.scalar_stabilized_trials += 1;
                        trial_stats =
                            stabilize_projected_after_scalar_trial(arena, originals, &mut trial)?;
                        false_count = positive_replay_false_count(arena, originals, &trial)?;
                    }
                    if false_count > current_false {
                        stats.scalar_rejected_worse_trials += 1;
                        continue;
                    }
                    if false_count == current_false && support_gain == 0 {
                        continue;
                    }
                    let replace =
                        best.as_ref()
                            .is_none_or(|(best_false, best_support_gain, _, _)| {
                                support_gain > *best_support_gain
                                    || (support_gain == *best_support_gain
                                        && false_count < *best_false)
                            });
                    if replace {
                        best = Some((false_count, support_gain, trial, trial_stats));
                    }
                }
                let Some((false_count, _, trial, trial_stats)) = best else {
                    continue;
                };
                *projected = trial;
                if false_count == current_false {
                    stats.scalar_equal_support_repairs += 1;
                }
                current_false = false_count;
                stats.absorb(trial_stats);
                stats.scalar_symbol_changes += 1;
                repairs += 1;
                changed_this_pass = true;
            }
        }
        if !changed_this_pass {
            break;
        }
    }
    Ok(stats)
}

fn stabilize_projected_after_scalar_trial(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
) -> Result<ProjectionRepairStats, SolverError> {
    let mut stats = ProjectionRepairStats::default();
    let select_stats =
        repair_projected_arrays_from_asserted_select_equalities(arena, originals, projected)?;
    stats.absorb(select_stats);
    let branch_stats = repair_projected_branch_disjunctions(arena, originals, projected)?;
    let branch_changes = branch_stats.changes();
    stats.absorb(branch_stats);
    if branch_changes > 0 {
        let after_branch_select =
            repair_projected_arrays_from_asserted_select_equalities(arena, originals, projected)?;
        stats.absorb(after_branch_select);
    }
    Ok(stats)
}

fn repair_projected_branch_disjunctions(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
) -> Result<ProjectionRepairStats, SolverError> {
    let ir =
        |e: axeyum_ir::IrError| SolverError::Backend(format!("lazy-ext branch repair failed: {e}"));
    let mut stats = ProjectionRepairStats::default();
    let mut conjuncts = Vec::new();
    for &assertion in originals {
        conjuncts.clear();
        collect_positive_conjuncts(arena, assertion, &mut conjuncts);
        for &conjunct in &conjuncts {
            if !matches!(arena.node(conjunct), TermNode::App { op: Op::BoolOr, .. }) {
                continue;
            }
            if eval(arena, conjunct, projected).map_err(ir)? != Value::Bool(false) {
                continue;
            }
            let Some(or_failure) = replay_failed_or_details(arena, conjunct, projected)? else {
                continue;
            };
            if let Some(schedule_stats) = repair_projected_branch_schedule(
                arena,
                originals,
                or_failure.best_branch_term,
                projected,
            )? {
                stats.absorb(schedule_stats);
                continue;
            }
            if or_failure.best_branch_false_literals != 1 {
                continue;
            }
            let Some(false_literal) = or_failure.best_branch_first_false_term else {
                continue;
            };
            if let Some(target) = store_base_repair_target(arena, false_literal) {
                if repair_projected_store_base_literal(
                    arena, originals, projected, target, false, &mut stats,
                )? {
                    continue;
                }
            }
            if let Some((lhs_symbol, rhs_symbol)) =
                direct_array_equality_repair_target(arena, false_literal)
            {
                if repair_projected_array_equality_literal(
                    arena, originals, projected, lhs_symbol, rhs_symbol, &mut stats,
                )? {
                    continue;
                }
            }
            let Some((symbol, value_term)) =
                direct_symbol_equality_repair_target(arena, false_literal)
            else {
                continue;
            };
            stats.branch_candidates += 1;
            let value = eval(arena, value_term, projected).map_err(ir)?;
            if store_projected_symbol_value(arena, projected, symbol, value)? {
                stats.branch_symbol_changes += 1;
            }
        }
    }
    Ok(stats)
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

#[derive(Clone, Copy)]
struct ExtProgress<'a> {
    round: usize,
    ctx: &'a RowCtx,
    row_lemmas: usize,
    cong_lemmas: usize,
    diff_skolems: usize,
    working_assertions: usize,
}

impl ExtProgress<'_> {
    fn fields(self) -> String {
        format!(
            "round={}, sites={}, array_eq_atoms={}, row_lemmas={}, cong_lemmas={}, \
             diff_skolems={}, working_assertions={}",
            self.round,
            self.ctx.sites.len(),
            self.ctx.eq_atoms.len(),
            self.row_lemmas,
            self.cong_lemmas,
            self.diff_skolems,
            self.working_assertions
        )
    }
}

fn ext_unknown_with_progress_note(
    detail: &str,
    progress: ExtProgress<'_>,
    note: Option<String>,
) -> CheckResult {
    let fields = match note {
        Some(note) => format!("{}, {note}", progress.fields()),
        None => progress.fields(),
    };
    ext_unknown(format!("{detail} ({fields})"))
}

fn ext_contextual_unknown_note(
    context: &str,
    progress: ExtProgress<'_>,
    reason: &UnknownReason,
    note: Option<String>,
) -> CheckResult {
    let fields = match note {
        Some(note) => format!("{}, {note}", progress.fields()),
        None => progress.fields(),
    };
    CheckResult::Unknown(UnknownReason {
        kind: reason.kind,
        detail: format!("{context} ({fields}): {}", reason.detail),
    })
}

enum LastExtReplay {
    Sat(Model),
    Failed(Box<ReplayFailure>),
    Error,
    Missing,
}

impl LastExtReplay {
    fn note(&self) -> Option<String> {
        match self {
            LastExtReplay::Failed(failure) => Some(failure.note()),
            LastExtReplay::Error => Some("last_candidate_replay=error".to_owned()),
            LastExtReplay::Sat(_) | LastExtReplay::Missing => None,
        }
    }
}

fn replay_last_ext_candidate(
    arena: &TermArena,
    ctx: &RowCtx,
    originals: &[TermId],
    assignment: Option<&Assignment>,
) -> LastExtReplay {
    let Some(assignment) = assignment else {
        return LastExtReplay::Missing;
    };
    match project_replay_ext_candidate(arena, ctx, originals, assignment) {
        Ok(ExtReplay::Sat(model)) => LastExtReplay::Sat(model),
        Ok(ExtReplay::Failed(failure)) => LastExtReplay::Failed(failure),
        Err(_) => LastExtReplay::Error,
    }
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
    let mut last_candidate: Option<Assignment> = None;

    for round in 0..MAX_ROW_ROUNDS {
        if past_deadline(deadline) {
            let replay = replay_last_ext_candidate(arena, ctx, originals, last_candidate.as_ref());
            let replay_note = match replay {
                LastExtReplay::Sat(model) => return Ok(CheckResult::Sat(model)),
                other => other.note(),
            };
            return Ok(ext_unknown_with_progress_note(
                "lazy-extensionality deadline exceeded before refinement converged",
                ExtProgress {
                    round,
                    ctx,
                    row_lemmas: added_row.len(),
                    cong_lemmas: added_cong.len(),
                    diff_skolems,
                    working_assertions: working.len(),
                },
                replay_note,
            ));
        }
        let round_config = config_with_remaining_deadline(config, deadline);
        let assignment = match check_scalar_abstraction(backend, arena, &working, &round_config)? {
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(reason) => {
                let replay =
                    replay_last_ext_candidate(arena, ctx, originals, last_candidate.as_ref());
                let replay_note = match replay {
                    LastExtReplay::Sat(model) => return Ok(CheckResult::Sat(model)),
                    other => other.note(),
                };
                return Ok(ext_contextual_unknown_note(
                    "lazy-extensionality scalar backend declined",
                    ExtProgress {
                        round,
                        ctx,
                        row_lemmas: added_row.len(),
                        cong_lemmas: added_cong.len(),
                        diff_skolems,
                        working_assertions: working.len(),
                    },
                    &reason,
                    replay_note,
                ));
            }
            CheckResult::Sat(model) => complete_assignment(arena, &model.to_assignment()),
        };
        last_candidate = Some(assignment.clone());

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

    let replay = replay_last_ext_candidate(arena, ctx, originals, last_candidate.as_ref());
    let replay_note = match replay {
        LastExtReplay::Sat(model) => return Ok(CheckResult::Sat(model)),
        other => other.note(),
    };
    Ok(ext_unknown_with_progress_note(
        &format!("lazy-extensionality refinement did not converge within {MAX_ROW_ROUNDS} rounds"),
        ExtProgress {
            round: MAX_ROW_ROUNDS,
            ctx,
            row_lemmas: added_row.len(),
            cong_lemmas: added_cong.len(),
            diff_skolems,
            working_assertions: working.len(),
        },
        replay_note,
    ))
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
    let indices = read_indices_for(arena, ctx, lhs, rhs);
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

/// The set of index terms worth checking for a true array equality `lhs = rhs`.
///
/// Equality implies `select(lhs, i) = select(rhs, i)` for *any* index term of
/// the right sort. Besides reads already materialised directly on the operands,
/// include every materialised compatible index (notably diff-skolems from other
/// array disequalities) and the finite store indices occurring inside the two
/// compared array terms. The latter closes store-chain equalities with no
/// external read at a write index; the former lets `a != b` witnesses interact
/// with surrounding store equalities.
fn read_indices_for(arena: &TermArena, ctx: &RowCtx, lhs: TermId, rhs: TermId) -> Vec<TermId> {
    let Some((index_sort, _)) = arena.sort_of(lhs).array_sorts() else {
        return Vec::new();
    };
    let mut indices: Vec<TermId> = Vec::new();
    for &(_, index) in ctx.memo.keys() {
        if arena.sort_of(index) == index_sort && !indices.contains(&index) {
            indices.push(index);
        }
    }
    collect_store_indices(arena, lhs, index_sort, &mut indices);
    collect_store_indices(arena, rhs, index_sort, &mut indices);
    // Deterministic order independent of hash-map iteration.
    indices.sort_by_key(|t| t.index());
    indices
}

fn collect_store_indices(arena: &TermArena, term: TermId, index_sort: Sort, out: &mut Vec<TermId>) {
    let TermNode::App { op, args } = arena.node(term) else {
        return;
    };
    match op {
        Op::Store => {
            if let Some(&index) = args.get(1)
                && arena.sort_of(index) == index_sort
                && !out.contains(&index)
            {
                out.push(index);
            }
            if let Some(&base) = args.first() {
                collect_store_indices(arena, base, index_sort, out);
            }
        }
        Op::Ite => {
            if let Some(&then_branch) = args.get(1) {
                collect_store_indices(arena, then_branch, index_sort, out);
            }
            if let Some(&else_branch) = args.get(2) {
                collect_store_indices(arena, else_branch, index_sort, out);
            }
        }
        _ => {}
    }
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
enum ExtReplay {
    Sat(Model),
    Failed(Box<ReplayFailure>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReplayEqFailure {
    lhs_term: TermId,
    rhs_term: TermId,
    lhs_value: String,
    rhs_value: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReplayScalarChoiceDiagnostic {
    target_symbol: SymbolId,
    value_term: TermId,
    value: String,
    changed: bool,
    literal_true: bool,
    branch_false_literals: usize,
    total_false_conjuncts: usize,
    first_global_false_ordinal: Option<usize>,
    first_global_false_term: Option<TermId>,
    first_global_false_eq: Option<ReplayEqFailure>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReplayBranchFalseLiteralDiagnostic {
    literal_term: TermId,
    eq: Option<ReplayEqFailure>,
    scalar_choices: Vec<ReplayScalarChoiceDiagnostic>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReplayScalarChainDiagnostic {
    branch_steps: Vec<ReplayScalarChoiceDiagnostic>,
    followup_steps: Vec<ReplayScalarChoiceDiagnostic>,
    final_branch_false_literals: usize,
    final_total_false_conjuncts: usize,
    final_global_false_ordinal: Option<usize>,
    final_global_false_term: Option<TermId>,
    final_global_false_eq: Option<ReplayEqFailure>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReplayBranchScalarClosureCandidateDiagnostic {
    branch_ordinal: usize,
    initial_false_literals: usize,
    repair_kind: String,
    repair_changes: usize,
    raw_branch_false_literals: Option<usize>,
    raw_total_false_conjuncts: Option<usize>,
    closure_steps: Vec<ReplayScalarChoiceDiagnostic>,
    final_branch_false_literals: Option<usize>,
    final_total_false_conjuncts: Option<usize>,
    final_global_false_ordinal: Option<usize>,
    final_global_false_term: Option<TermId>,
    final_global_false_eq: Option<ReplayEqFailure>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReplayBranchCandidateDiagnostic {
    branch_ordinal: usize,
    initial_false_literals: usize,
    status: String,
    final_false_literals: Option<usize>,
    total_false_conjuncts: Option<usize>,
    repair_changes: usize,
    first_false_term: Option<TermId>,
    first_false_eq: Option<ReplayEqFailure>,
    first_global_false_ordinal: Option<usize>,
    first_global_false_term: Option<TermId>,
    first_global_false_eq: Option<ReplayEqFailure>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReplayBranchPairCandidateDiagnostic {
    first_branch_ordinal: usize,
    second_or_ordinal: usize,
    second_or_term: TermId,
    second_branch_ordinal: usize,
    second_initial_false_literals: usize,
    status: String,
    first_repair_changes: usize,
    second_repair_changes: usize,
    second_final_false_literals: Option<usize>,
    total_false_conjuncts: Option<usize>,
    final_global_false_ordinal: Option<usize>,
    final_global_false_term: Option<TermId>,
    final_global_false_eq: Option<ReplayEqFailure>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReplayBranchSelectCandidateDiagnostic {
    branch_ordinal: usize,
    select_ordinal: usize,
    select_term: TermId,
    kind: String,
    status: String,
    branch_repair_changes: usize,
    select_repair_changes: usize,
    target_true: bool,
    total_false_conjuncts: Option<usize>,
    first_global_false_ordinal: Option<usize>,
    first_global_false_term: Option<TermId>,
    first_global_false_eq: Option<ReplayEqFailure>,
    first_global_false_or: Option<ReplayOrFailure>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReplaySelectCandidateDiagnostic {
    kind: String,
    status: String,
    repair_changes: usize,
    target_true: bool,
    total_false_conjuncts: Option<usize>,
    first_global_false_ordinal: Option<usize>,
    first_global_false_term: Option<TermId>,
    first_global_false_eq: Option<ReplayEqFailure>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReplayFailure {
    assertion_ordinal: usize,
    assertion_term: TermId,
    conjunct_ordinal: usize,
    conjunct_term: TermId,
    failed_eq: Option<ReplayEqFailure>,
    failed_or: Option<ReplayOrFailure>,
    select_candidate_diagnostics: Vec<ReplaySelectCandidateDiagnostic>,
    branch_candidate_diagnostics: Vec<ReplayBranchCandidateDiagnostic>,
    branch_select_candidate_diagnostics: Vec<ReplayBranchSelectCandidateDiagnostic>,
    branch_pair_candidate_diagnostics: Vec<ReplayBranchPairCandidateDiagnostic>,
    repair_stats: ProjectionRepairStats,
}

fn write_replay_or_false_literal_details(
    note: &mut String,
    prefix: &str,
    or_failure: &ReplayOrFailure,
) {
    if or_failure.best_branch_false_literal_details.is_empty() {
        return;
    }
    let _ = write!(note, ", {prefix}_best_branch_false_literal_details=[");
    for (literal_idx, detail) in or_failure
        .best_branch_false_literal_details
        .iter()
        .enumerate()
    {
        if literal_idx > 0 {
            let _ = write!(note, "; ");
        }
        let _ = write!(note, "#{literal_idx}:term={}", detail.literal_term.index());
        if let Some(eq) = &detail.eq {
            let _ = write!(
                note,
                ",lhs_term={},rhs_term={},lhs_value={},rhs_value={}",
                eq.lhs_term.index(),
                eq.rhs_term.index(),
                eq.lhs_value,
                eq.rhs_value
            );
        }
        if detail.scalar_choices.is_empty() {
            continue;
        }
        let _ = write!(note, ",scalar_choices=(");
        for (choice_idx, choice) in detail.scalar_choices.iter().enumerate() {
            if choice_idx > 0 {
                let _ = write!(note, "|");
            }
            write_scalar_choice_effect(note, choice_idx, choice);
        }
        let _ = write!(note, ")");
    }
    let _ = write!(note, "]");
}

fn write_scalar_choice_effect(
    note: &mut String,
    choice_idx: usize,
    choice: &ReplayScalarChoiceDiagnostic,
) {
    let _ = write!(
        note,
        "#{}:symbol={},value_term={},value={},changed={},literal_true={},\
         branch_false={},total_false={}",
        choice_idx,
        choice.target_symbol.index(),
        choice.value_term.index(),
        choice.value,
        choice.changed,
        choice.literal_true,
        choice.branch_false_literals,
        choice.total_false_conjuncts
    );
    if let Some(ordinal) = choice.first_global_false_ordinal {
        let _ = write!(note, ",global_false_ordinal={ordinal}");
    }
    if let Some(term) = choice.first_global_false_term {
        let _ = write!(note, ",global_false_term={}", term.index());
    }
    if let Some(eq) = &choice.first_global_false_eq {
        let _ = write!(
            note,
            ",global_false_lhs_term={},global_false_rhs_term={},\
             global_false_lhs_value={},global_false_rhs_value={}",
            eq.lhs_term.index(),
            eq.rhs_term.index(),
            eq.lhs_value,
            eq.rhs_value
        );
    }
}

fn write_scalar_choice_effect_list(note: &mut String, choices: &[ReplayScalarChoiceDiagnostic]) {
    let _ = write!(note, "[");
    for (idx, choice) in choices.iter().enumerate() {
        if idx > 0 {
            let _ = write!(note, "|");
        }
        write_scalar_choice_effect(note, idx, choice);
    }
    let _ = write!(note, "]");
}

fn write_replay_or_paired_scalar_chain(
    note: &mut String,
    prefix: &str,
    or_failure: &ReplayOrFailure,
) {
    let Some(chain) = &or_failure.best_branch_paired_scalar_chain else {
        return;
    };
    let _ = write!(note, ", {prefix}_best_branch_paired_scalar_chain=(");
    let _ = write!(note, "branch_steps=");
    write_scalar_choice_effect_list(note, &chain.branch_steps);
    let _ = write!(note, ",followup_steps=");
    write_scalar_choice_effect_list(note, &chain.followup_steps);
    let _ = write!(
        note,
        ",final_branch_false={},final_total_false={}",
        chain.final_branch_false_literals, chain.final_total_false_conjuncts
    );
    if let Some(ordinal) = chain.final_global_false_ordinal {
        let _ = write!(note, ",final_global_false_ordinal={ordinal}");
    }
    if let Some(term) = chain.final_global_false_term {
        let _ = write!(note, ",final_global_false_term={}", term.index());
    }
    if let Some(eq) = &chain.final_global_false_eq {
        let _ = write!(
            note,
            ",final_global_false_lhs_term={},final_global_false_rhs_term={},\
             final_global_false_lhs_value={},final_global_false_rhs_value={}",
            eq.lhs_term.index(),
            eq.rhs_term.index(),
            eq.lhs_value,
            eq.rhs_value
        );
    }
    let _ = write!(note, ")");
}

fn write_replay_or_scalar_closure_branch_candidates(
    note: &mut String,
    prefix: &str,
    or_failure: &ReplayOrFailure,
) {
    if or_failure.scalar_closure_branch_candidates.is_empty() {
        return;
    }
    let _ = write!(note, ", {prefix}_scalar_closure_branch_candidates=[");
    for (idx, candidate) in or_failure
        .scalar_closure_branch_candidates
        .iter()
        .enumerate()
    {
        if idx > 0 {
            let _ = write!(note, "; ");
        }
        let _ = write!(
            note,
            "#{}:init={},repair={},changes={}",
            candidate.branch_ordinal,
            candidate.initial_false_literals,
            candidate.repair_kind,
            candidate.repair_changes
        );
        if let Some(raw_branch_false) = candidate.raw_branch_false_literals {
            let _ = write!(note, ",raw_branch_false={raw_branch_false}");
        }
        if let Some(raw_total_false) = candidate.raw_total_false_conjuncts {
            let _ = write!(note, ",raw_total_false={raw_total_false}");
        }
        if !candidate.closure_steps.is_empty() {
            let _ = write!(note, ",closure_steps=");
            write_scalar_choice_effect_list(note, &candidate.closure_steps);
        }
        if let Some(final_branch_false) = candidate.final_branch_false_literals {
            let _ = write!(note, ",final_branch_false={final_branch_false}");
        }
        if let Some(final_total_false) = candidate.final_total_false_conjuncts {
            let _ = write!(note, ",final_total_false={final_total_false}");
        }
        if let Some(ordinal) = candidate.final_global_false_ordinal {
            let _ = write!(note, ",final_global_false_ordinal={ordinal}");
        }
        if let Some(term) = candidate.final_global_false_term {
            let _ = write!(note, ",final_global_false_term={}", term.index());
        }
        if let Some(eq) = &candidate.final_global_false_eq {
            let _ = write!(
                note,
                ",final_global_false_lhs_term={},final_global_false_rhs_term={},\
                 final_global_false_lhs_value={},final_global_false_rhs_value={}",
                eq.lhs_term.index(),
                eq.rhs_term.index(),
                eq.lhs_value,
                eq.rhs_value
            );
        }
    }
    let _ = write!(note, "]");
}

impl ReplayFailure {
    #[allow(clippy::too_many_lines)]
    fn note(&self) -> String {
        let mut note = format!(
            "last_candidate_replay=false(assertion_ordinal={}, term={}, \
             failed_conjunct_ordinal={}, failed_conjunct_term={}, \
             select_repair_candidates={}, select_repair_array_changes={}, \
             select_repair_symbol_changes={}, branch_repair_candidates={}, \
             branch_repair_symbol_changes={}, scalar_repair_candidates={}, \
             scalar_support_candidates={}, scalar_stabilized_trials={}, \
             scalar_rejected_worse_trials={}, scalar_equal_support_repairs={}, \
             scalar_repair_symbol_changes={}, projection_repair_changes={})",
            self.assertion_ordinal,
            self.assertion_term.index(),
            self.conjunct_ordinal,
            self.conjunct_term.index(),
            self.repair_stats.candidates,
            self.repair_stats.array_changes,
            self.repair_stats.symbol_changes,
            self.repair_stats.branch_candidates,
            self.repair_stats.branch_symbol_changes,
            self.repair_stats.scalar_candidates,
            self.repair_stats.scalar_support_candidates,
            self.repair_stats.scalar_stabilized_trials,
            self.repair_stats.scalar_rejected_worse_trials,
            self.repair_stats.scalar_equal_support_repairs,
            self.repair_stats.scalar_symbol_changes,
            self.repair_stats.changes()
        );
        if let Some(eq) = &self.failed_eq {
            let _ = write!(
                note,
                ", failed_eq_lhs_term={}, failed_eq_rhs_term={}, \
                 failed_eq_lhs_value={}, failed_eq_rhs_value={}",
                eq.lhs_term.index(),
                eq.rhs_term.index(),
                eq.lhs_value,
                eq.rhs_value
            );
        }
        if let Some(or_failure) = &self.failed_or {
            let _ = write!(
                note,
                ", failed_or_branches={}, failed_or_best_branch={}, \
                 failed_or_best_branch_false_literals={}, \
                 failed_or_best_branch_total_literals={}",
                or_failure.branch_count,
                or_failure.best_branch_ordinal,
                or_failure.best_branch_false_literals,
                or_failure.best_branch_total_literals
            );
            if let Some(term) = or_failure.best_branch_first_false_term {
                let _ = write!(
                    note,
                    ", failed_or_best_branch_first_false_term={}",
                    term.index()
                );
            }
            if let Some(eq) = &or_failure.best_branch_first_false_eq {
                let _ = write!(
                    note,
                    ", failed_or_best_branch_first_false_lhs_term={}, \
                     failed_or_best_branch_first_false_rhs_term={}, \
                     failed_or_best_branch_first_false_lhs_value={}, \
                     failed_or_best_branch_first_false_rhs_value={}",
                    eq.lhs_term.index(),
                    eq.rhs_term.index(),
                    eq.lhs_value,
                    eq.rhs_value
                );
            }
            write_replay_or_false_literal_details(&mut note, "failed_or", or_failure);
            write_replay_or_paired_scalar_chain(&mut note, "failed_or", or_failure);
            write_replay_or_scalar_closure_branch_candidates(&mut note, "failed_or", or_failure);
        }
        if !self.select_candidate_diagnostics.is_empty() {
            let _ = write!(note, ", select_candidate_diagnostics=[");
            for (idx, diagnostic) in self.select_candidate_diagnostics.iter().enumerate() {
                if idx > 0 {
                    let _ = write!(note, "; ");
                }
                let _ = write!(
                    note,
                    "{}:status={},changes={},target_true={}",
                    diagnostic.kind,
                    diagnostic.status,
                    diagnostic.repair_changes,
                    diagnostic.target_true
                );
                if let Some(total_false) = diagnostic.total_false_conjuncts {
                    let _ = write!(note, ",total_false={total_false}");
                }
                if let Some(ordinal) = diagnostic.first_global_false_ordinal {
                    let _ = write!(note, ",global_false_ordinal={ordinal}");
                }
                if let Some(term) = diagnostic.first_global_false_term {
                    let _ = write!(note, ",global_false_term={}", term.index());
                }
                if let Some(eq) = &diagnostic.first_global_false_eq {
                    let _ = write!(
                        note,
                        ",global_false_lhs_term={},global_false_rhs_term={},\
                         global_false_lhs_value={},global_false_rhs_value={}",
                        eq.lhs_term.index(),
                        eq.rhs_term.index(),
                        eq.lhs_value,
                        eq.rhs_value
                    );
                }
            }
            let _ = write!(note, "]");
        }
        if !self.branch_candidate_diagnostics.is_empty() {
            let _ = write!(note, ", branch_candidate_diagnostics=[");
            for (idx, diagnostic) in self.branch_candidate_diagnostics.iter().enumerate() {
                if idx > 0 {
                    let _ = write!(note, "; ");
                }
                let _ = write!(
                    note,
                    "#{}:init={},status={},changes={}",
                    diagnostic.branch_ordinal,
                    diagnostic.initial_false_literals,
                    diagnostic.status,
                    diagnostic.repair_changes
                );
                if let Some(final_false) = diagnostic.final_false_literals {
                    let _ = write!(note, ",final={final_false}");
                }
                if let Some(total_false) = diagnostic.total_false_conjuncts {
                    let _ = write!(note, ",total_false={total_false}");
                }
                if let Some(term) = diagnostic.first_false_term {
                    let _ = write!(note, ",first_false_term={}", term.index());
                }
                if let Some(eq) = &diagnostic.first_false_eq {
                    let _ = write!(
                        note,
                        ",first_false_lhs_term={},first_false_rhs_term={},\
                         first_false_lhs_value={},first_false_rhs_value={}",
                        eq.lhs_term.index(),
                        eq.rhs_term.index(),
                        eq.lhs_value,
                        eq.rhs_value
                    );
                }
                if let Some(ordinal) = diagnostic.first_global_false_ordinal {
                    let _ = write!(note, ",global_false_ordinal={ordinal}");
                }
                if let Some(term) = diagnostic.first_global_false_term {
                    let _ = write!(note, ",global_false_term={}", term.index());
                }
                if let Some(eq) = &diagnostic.first_global_false_eq {
                    let _ = write!(
                        note,
                        ",global_false_lhs_term={},global_false_rhs_term={},\
                         global_false_lhs_value={},global_false_rhs_value={}",
                        eq.lhs_term.index(),
                        eq.rhs_term.index(),
                        eq.lhs_value,
                        eq.rhs_value
                    );
                }
            }
            let _ = write!(note, "]");
        }
        if !self.branch_select_candidate_diagnostics.is_empty() {
            let _ = write!(note, ", branch_select_candidate_diagnostics=[");
            for (idx, diagnostic) in self.branch_select_candidate_diagnostics.iter().enumerate() {
                if idx > 0 {
                    let _ = write!(note, "; ");
                }
                let _ = write!(
                    note,
                    "#{}->{}:{},status={},branch_changes={},select_changes={},\
                     target_true={},select_term={}",
                    diagnostic.branch_ordinal,
                    diagnostic.select_ordinal,
                    diagnostic.kind,
                    diagnostic.status,
                    diagnostic.branch_repair_changes,
                    diagnostic.select_repair_changes,
                    diagnostic.target_true,
                    diagnostic.select_term.index()
                );
                if let Some(total_false) = diagnostic.total_false_conjuncts {
                    let _ = write!(note, ",total_false={total_false}");
                }
                if let Some(ordinal) = diagnostic.first_global_false_ordinal {
                    let _ = write!(note, ",global_false_ordinal={ordinal}");
                }
                if let Some(term) = diagnostic.first_global_false_term {
                    let _ = write!(note, ",global_false_term={}", term.index());
                }
                if let Some(eq) = &diagnostic.first_global_false_eq {
                    let _ = write!(
                        note,
                        ",global_false_lhs_term={},global_false_rhs_term={},\
                         global_false_lhs_value={},global_false_rhs_value={}",
                        eq.lhs_term.index(),
                        eq.rhs_term.index(),
                        eq.lhs_value,
                        eq.rhs_value
                    );
                }
                if let Some(or_failure) = &diagnostic.first_global_false_or {
                    let _ = write!(
                        note,
                        ",global_false_or_branches={},global_false_or_best_branch={},\
                         global_false_or_best_branch_false_literals={},\
                         global_false_or_best_branch_total_literals={}",
                        or_failure.branch_count,
                        or_failure.best_branch_ordinal,
                        or_failure.best_branch_false_literals,
                        or_failure.best_branch_total_literals
                    );
                    if let Some(term) = or_failure.best_branch_first_false_term {
                        let _ = write!(
                            note,
                            ",global_false_or_best_branch_first_false_term={}",
                            term.index()
                        );
                    }
                    if let Some(eq) = &or_failure.best_branch_first_false_eq {
                        let _ = write!(
                            note,
                            ",global_false_or_best_branch_first_false_lhs_term={},\
                             global_false_or_best_branch_first_false_rhs_term={},\
                             global_false_or_best_branch_first_false_lhs_value={},\
                             global_false_or_best_branch_first_false_rhs_value={}",
                            eq.lhs_term.index(),
                            eq.rhs_term.index(),
                            eq.lhs_value,
                            eq.rhs_value
                        );
                    }
                    write_replay_or_false_literal_details(&mut note, "global_false_or", or_failure);
                    write_replay_or_paired_scalar_chain(&mut note, "global_false_or", or_failure);
                    write_replay_or_scalar_closure_branch_candidates(
                        &mut note,
                        "global_false_or",
                        or_failure,
                    );
                }
            }
            let _ = write!(note, "]");
        }
        if !self.branch_pair_candidate_diagnostics.is_empty() {
            let _ = write!(note, ", branch_pair_candidate_diagnostics=[");
            for (idx, diagnostic) in self.branch_pair_candidate_diagnostics.iter().enumerate() {
                if idx > 0 {
                    let _ = write!(note, "; ");
                }
                let _ = write!(
                    note,
                    "#{}->{}#{}:init={},status={},first_changes={},second_changes={}",
                    diagnostic.first_branch_ordinal,
                    diagnostic.second_or_ordinal,
                    diagnostic.second_branch_ordinal,
                    diagnostic.second_initial_false_literals,
                    diagnostic.status,
                    diagnostic.first_repair_changes,
                    diagnostic.second_repair_changes
                );
                let _ = write!(
                    note,
                    ",second_or_term={}",
                    diagnostic.second_or_term.index()
                );
                if let Some(final_false) = diagnostic.second_final_false_literals {
                    let _ = write!(note, ",final={final_false}");
                }
                if let Some(total_false) = diagnostic.total_false_conjuncts {
                    let _ = write!(note, ",total_false={total_false}");
                }
                if let Some(ordinal) = diagnostic.final_global_false_ordinal {
                    let _ = write!(note, ",global_false_ordinal={ordinal}");
                }
                if let Some(term) = diagnostic.final_global_false_term {
                    let _ = write!(note, ",global_false_term={}", term.index());
                }
                if let Some(eq) = &diagnostic.final_global_false_eq {
                    let _ = write!(
                        note,
                        ",global_false_lhs_term={},global_false_rhs_term={},\
                         global_false_lhs_value={},global_false_rhs_value={}",
                        eq.lhs_term.index(),
                        eq.rhs_term.index(),
                        eq.lhs_value,
                        eq.rhs_value
                    );
                }
            }
            let _ = write!(note, "]");
        }
        note
    }
}

fn project_replay_ext(
    arena: &TermArena,
    ctx: &RowCtx,
    originals: &[TermId],
    assignment: &Assignment,
) -> Result<CheckResult, SolverError> {
    match project_replay_ext_candidate(arena, ctx, originals, assignment)? {
        ExtReplay::Sat(model) => Ok(CheckResult::Sat(model)),
        ExtReplay::Failed(failure) => Ok(ext_unknown(format!(
            "lazy-extensionality candidate failed replay: assertion #{} evaluated to \
             false (top-level ordinal {}, first false conjunct ordinal {}, term {}, \
             incomplete on this shape)",
            failure.assertion_term.index(),
            failure.assertion_ordinal,
            failure.conjunct_ordinal,
            failure.conjunct_term.index()
        ))),
    }
}

fn repair_projected_ext_candidate(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
) -> Result<ProjectionRepairStats, SolverError> {
    const MAX_PROJECTION_REPAIR_ROUNDS: usize = 32;

    let mut repair_stats = ProjectionRepairStats::default();
    for _ in 0..MAX_PROJECTION_REPAIR_ROUNDS {
        let select_stats =
            repair_projected_arrays_from_asserted_select_equalities(arena, originals, projected)?;
        let mut changes = select_stats.changes();
        repair_stats.absorb(select_stats);
        let branch_stats = repair_projected_branch_disjunctions(arena, originals, projected)?;
        let branch_changes = branch_stats.changes();
        changes += branch_changes;
        repair_stats.absorb(branch_stats);
        if branch_changes > 0 {
            let after_branch_select = repair_projected_arrays_from_asserted_select_equalities(
                arena, originals, projected,
            )?;
            changes += after_branch_select.changes();
            repair_stats.absorb(after_branch_select);
        }
        let scalar_stats = repair_projected_scalar_equalities(arena, originals, projected)?;
        let scalar_changes = scalar_stats.changes();
        changes += scalar_changes;
        repair_stats.absorb(scalar_stats);
        if changes == 0 {
            break;
        }
    }

    let final_branch_stats = repair_projected_branch_disjunctions(arena, originals, projected)?;
    repair_stats.absorb(final_branch_stats);
    let final_select_stats =
        repair_projected_arrays_from_asserted_select_equalities(arena, originals, projected)?;
    repair_stats.absorb(final_select_stats);
    let final_scalar_stats = repair_projected_scalar_equalities(arena, originals, projected)?;
    let final_scalar_changes = final_scalar_stats.changes();
    repair_stats.absorb(final_scalar_stats);
    if final_scalar_changes > 0 {
        let after_scalar_select =
            repair_projected_arrays_from_asserted_select_equalities(arena, originals, projected)?;
        repair_stats.absorb(after_scalar_select);
        let after_scalar_branch =
            repair_projected_branch_disjunctions(arena, originals, projected)?;
        let after_scalar_branch_changes = after_scalar_branch.changes();
        repair_stats.absorb(after_scalar_branch);
        if after_scalar_branch_changes > 0 {
            let after_scalar_branch_select =
                repair_projected_arrays_from_asserted_select_equalities(
                    arena, originals, projected,
                )?;
            repair_stats.absorb(after_scalar_branch_select);
        }
        let after_scalar_stabilizing_scalar =
            repair_projected_scalar_equalities(arena, originals, projected)?;
        let after_scalar_stabilizing_scalar_changes = after_scalar_stabilizing_scalar.changes();
        repair_stats.absorb(after_scalar_stabilizing_scalar);
        if after_scalar_stabilizing_scalar_changes > 0 {
            let after_stabilizing_scalar_branch =
                repair_projected_branch_disjunctions(arena, originals, projected)?;
            let after_stabilizing_scalar_branch_changes = after_stabilizing_scalar_branch.changes();
            repair_stats.absorb(after_stabilizing_scalar_branch);
            if after_stabilizing_scalar_branch_changes > 0 {
                let after_stabilizing_scalar_select =
                    repair_projected_arrays_from_asserted_select_equalities(
                        arena, originals, projected,
                    )?;
                repair_stats.absorb(after_stabilizing_scalar_select);
            }
        }
    }
    Ok(repair_stats)
}

fn first_projected_replay_failure(
    arena: &TermArena,
    originals: &[TermId],
    projected: &Assignment,
    repair_stats: ProjectionRepairStats,
) -> Result<Option<ReplayFailure>, SolverError> {
    for (ordinal, &assertion) in originals.iter().enumerate() {
        match eval(arena, assertion, projected) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Ok(Some(first_false_replay_conjunct(
                    arena,
                    assertion,
                    ordinal,
                    projected,
                    repair_stats,
                )?));
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
    Ok(None)
}

fn branch_first_false_literal(
    arena: &TermArena,
    branch: TermId,
    assignment: &Assignment,
) -> Result<Option<TermId>, SolverError> {
    let mut literals = Vec::new();
    collect_positive_conjuncts(arena, branch, &mut literals);
    for literal in literals {
        match eval(arena, literal, assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => return Ok(Some(literal)),
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "lazy-ext branch diagnostic: literal #{} evaluated to non-Boolean {value}",
                    literal.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "lazy-ext branch diagnostic: literal #{} failed evaluation: {error}",
                    literal.index()
                )));
            }
        }
    }
    Ok(None)
}

#[allow(clippy::single_match_else)]
fn replay_branch_candidate_diagnostics(
    arena: &TermArena,
    originals: &[TermId],
    branch_disjunction: TermId,
    projected: &Assignment,
) -> Result<Vec<ReplayBranchCandidateDiagnostic>, SolverError> {
    if !matches!(
        arena.node(branch_disjunction),
        TermNode::App { op: Op::BoolOr, .. }
    ) {
        return Ok(Vec::new());
    }

    let current_total_false = positive_replay_false_count(arena, originals, projected)?;
    let mut branches = Vec::new();
    collect_positive_disjuncts(arena, branch_disjunction, &mut branches);
    let mut diagnostics = Vec::new();
    for (branch_ordinal, branch) in branches.into_iter().enumerate() {
        let initial_false = branch_false_literal_count(arena, branch, projected)?;
        let mut trial = projected.clone();
        match repair_projected_branch_as_candidate(arena, originals, branch, &mut trial)? {
            Some(stats) => {
                let final_false = branch_false_literal_count(arena, branch, &trial)?;
                let total_false = positive_replay_false_count(arena, originals, &trial)?;
                let first_false = branch_first_false_literal(arena, branch, &trial)?;
                let global_failure = first_projected_replay_failure(
                    arena,
                    originals,
                    &trial,
                    ProjectionRepairStats::default(),
                )?;
                diagnostics.push(ReplayBranchCandidateDiagnostic {
                    branch_ordinal,
                    initial_false_literals: initial_false,
                    status: if total_false > current_total_false {
                        "worse_full_replay".to_owned()
                    } else {
                        "candidate".to_owned()
                    },
                    final_false_literals: Some(final_false),
                    total_false_conjuncts: Some(total_false),
                    repair_changes: stats.changes(),
                    first_false_term: first_false,
                    first_false_eq: match first_false {
                        Some(term) => replay_failed_eq_details(arena, term, &trial)?,
                        None => None,
                    },
                    first_global_false_ordinal: global_failure
                        .as_ref()
                        .map(|failure| failure.conjunct_ordinal),
                    first_global_false_term: global_failure
                        .as_ref()
                        .map(|failure| failure.conjunct_term),
                    first_global_false_eq: global_failure.and_then(|failure| failure.failed_eq),
                });
            }
            None => {
                let first_false = branch_first_false_literal(arena, branch, projected)?;
                diagnostics.push(ReplayBranchCandidateDiagnostic {
                    branch_ordinal,
                    initial_false_literals: initial_false,
                    status: "no_repair".to_owned(),
                    final_false_literals: Some(initial_false),
                    total_false_conjuncts: None,
                    repair_changes: 0,
                    first_false_term: first_false,
                    first_false_eq: match first_false {
                        Some(term) => replay_failed_eq_details(arena, term, projected)?,
                        None => None,
                    },
                    first_global_false_ordinal: None,
                    first_global_false_term: None,
                    first_global_false_eq: None,
                });
            }
        }
    }
    Ok(diagnostics)
}

fn branch_pair_candidate_status(
    arena: &TermArena,
    first_disjunction: TermId,
    second_disjunction: TermId,
    assignment: &Assignment,
    total_false: usize,
    current_total_false: usize,
) -> Result<String, SolverError> {
    let ir = |error| SolverError::Backend(format!("lazy-ext pair diagnostic failed: {error}"));
    if eval(arena, first_disjunction, assignment).map_err(ir)? != Value::Bool(true)
        || eval(arena, second_disjunction, assignment).map_err(ir)? != Value::Bool(true)
    {
        return Ok("breaks_pair_or".to_owned());
    }
    Ok(match total_false.cmp(&current_total_false) {
        std::cmp::Ordering::Greater => "worse_full_replay".to_owned(),
        std::cmp::Ordering::Equal => "same_full_replay".to_owned(),
        std::cmp::Ordering::Less => "candidate".to_owned(),
    })
}

struct BranchPairDiagnosticBase<'a> {
    arena: &'a TermArena,
    originals: &'a [TermId],
    first_disjunction: TermId,
    current_total_false: usize,
    first_trial: &'a Assignment,
    first_branch_ordinal: usize,
    first_repair_changes: usize,
    second_or_ordinal: usize,
    second_or_term: TermId,
}

fn replay_branch_pair_second_candidate_diagnostic(
    base: &BranchPairDiagnosticBase<'_>,
    second_branch_ordinal: usize,
    second_branch: TermId,
) -> Result<ReplayBranchPairCandidateDiagnostic, SolverError> {
    let second_initial_false =
        branch_false_literal_count(base.arena, second_branch, base.first_trial)?;
    let mut pair_trial = base.first_trial.clone();
    let Some(second_stats) = repair_projected_branch_as_candidate(
        base.arena,
        base.originals,
        second_branch,
        &mut pair_trial,
    )?
    else {
        return Ok(ReplayBranchPairCandidateDiagnostic {
            first_branch_ordinal: base.first_branch_ordinal,
            second_or_ordinal: base.second_or_ordinal,
            second_or_term: base.second_or_term,
            second_branch_ordinal,
            second_initial_false_literals: second_initial_false,
            status: "no_repair".to_owned(),
            first_repair_changes: base.first_repair_changes,
            second_repair_changes: 0,
            second_final_false_literals: Some(second_initial_false),
            total_false_conjuncts: None,
            final_global_false_ordinal: None,
            final_global_false_term: None,
            final_global_false_eq: None,
        });
    };

    let second_final_false = branch_false_literal_count(base.arena, second_branch, &pair_trial)?;
    let total_false = positive_replay_false_count(base.arena, base.originals, &pair_trial)?;
    let status = branch_pair_candidate_status(
        base.arena,
        base.first_disjunction,
        base.second_or_term,
        &pair_trial,
        total_false,
        base.current_total_false,
    )?;
    let global_failure = first_projected_replay_failure(
        base.arena,
        base.originals,
        &pair_trial,
        ProjectionRepairStats::default(),
    )?;
    Ok(ReplayBranchPairCandidateDiagnostic {
        first_branch_ordinal: base.first_branch_ordinal,
        second_or_ordinal: base.second_or_ordinal,
        second_or_term: base.second_or_term,
        second_branch_ordinal,
        second_initial_false_literals: second_initial_false,
        status,
        first_repair_changes: base.first_repair_changes,
        second_repair_changes: second_stats.changes(),
        second_final_false_literals: Some(second_final_false),
        total_false_conjuncts: Some(total_false),
        final_global_false_ordinal: global_failure
            .as_ref()
            .map(|failure| failure.conjunct_ordinal),
        final_global_false_term: global_failure.as_ref().map(|failure| failure.conjunct_term),
        final_global_false_eq: global_failure.and_then(|failure| failure.failed_eq),
    })
}

fn replay_branch_pair_candidate_diagnostics(
    arena: &TermArena,
    originals: &[TermId],
    branch_disjunction: TermId,
    projected: &Assignment,
) -> Result<Vec<ReplayBranchPairCandidateDiagnostic>, SolverError> {
    const MAX_BRANCH_PAIR_DIAGNOSTICS: usize = 16;

    if !matches!(
        arena.node(branch_disjunction),
        TermNode::App { op: Op::BoolOr, .. }
    ) {
        return Ok(Vec::new());
    }

    let current_total_false = positive_replay_false_count(arena, originals, projected)?;
    let mut first_branches = Vec::new();
    collect_positive_disjuncts(arena, branch_disjunction, &mut first_branches);
    let mut diagnostics = Vec::new();
    for (first_ordinal, first_branch) in first_branches.into_iter().enumerate() {
        let mut first_trial = projected.clone();
        let Some(first_stats) =
            repair_projected_branch_as_candidate(arena, originals, first_branch, &mut first_trial)?
        else {
            continue;
        };
        let Some(second_failure) = first_projected_replay_failure(
            arena,
            originals,
            &first_trial,
            ProjectionRepairStats::default(),
        )?
        else {
            continue;
        };
        if second_failure.conjunct_term == branch_disjunction
            || !matches!(
                arena.node(second_failure.conjunct_term),
                TermNode::App { op: Op::BoolOr, .. }
            )
        {
            continue;
        }

        let mut second_branches = Vec::new();
        collect_positive_disjuncts(arena, second_failure.conjunct_term, &mut second_branches);
        let base = BranchPairDiagnosticBase {
            arena,
            originals,
            first_disjunction: branch_disjunction,
            current_total_false,
            first_trial: &first_trial,
            first_branch_ordinal: first_ordinal,
            first_repair_changes: first_stats.changes(),
            second_or_ordinal: second_failure.conjunct_ordinal,
            second_or_term: second_failure.conjunct_term,
        };
        for (second_ordinal, second_branch) in second_branches.into_iter().enumerate() {
            if diagnostics.len() >= MAX_BRANCH_PAIR_DIAGNOSTICS {
                return Ok(diagnostics);
            }
            diagnostics.push(replay_branch_pair_second_candidate_diagnostic(
                &base,
                second_ordinal,
                second_branch,
            )?);
        }
    }
    Ok(diagnostics)
}

fn select_candidate_status(target_true: bool, total_false: usize, current_false: usize) -> String {
    if !target_true {
        return "breaks_select".to_owned();
    }
    match total_false.cmp(&current_false) {
        std::cmp::Ordering::Greater => "worse_full_replay".to_owned(),
        std::cmp::Ordering::Equal => "same_full_replay".to_owned(),
        std::cmp::Ordering::Less => "candidate".to_owned(),
    }
}

fn replay_select_candidate_from_trial(
    arena: &TermArena,
    originals: &[TermId],
    failure: &ReplayFailure,
    current_false: usize,
    kind: &str,
    stats: ProjectionRepairStats,
    trial: &Assignment,
) -> Result<ReplaySelectCandidateDiagnostic, SolverError> {
    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext select diagnostic failed: {e}"))
    };
    let target_true = eval(arena, failure.conjunct_term, trial).map_err(ir)? == Value::Bool(true);
    let total_false = positive_replay_false_count(arena, originals, trial)?;
    let global_failure =
        first_projected_replay_failure(arena, originals, trial, ProjectionRepairStats::default())?;
    Ok(ReplaySelectCandidateDiagnostic {
        kind: kind.to_owned(),
        status: select_candidate_status(target_true, total_false, current_false),
        repair_changes: stats.changes(),
        target_true,
        total_false_conjuncts: Some(total_false),
        first_global_false_ordinal: global_failure
            .as_ref()
            .map(|failure| failure.conjunct_ordinal),
        first_global_false_term: global_failure.as_ref().map(|failure| failure.conjunct_term),
        first_global_false_eq: global_failure.and_then(|failure| failure.failed_eq),
    })
}

fn replay_unrepaired_select_candidate(
    kind: &str,
    stats: ProjectionRepairStats,
) -> ReplaySelectCandidateDiagnostic {
    ReplaySelectCandidateDiagnostic {
        kind: kind.to_owned(),
        status: "no_repair".to_owned(),
        repair_changes: stats.changes(),
        target_true: false,
        total_false_conjuncts: None,
        first_global_false_ordinal: None,
        first_global_false_term: None,
        first_global_false_eq: None,
    }
}

fn replay_select_candidate_diagnostics(
    arena: &TermArena,
    originals: &[TermId],
    projected: &Assignment,
    failure: &ReplayFailure,
) -> Result<Vec<ReplaySelectCandidateDiagnostic>, SolverError> {
    let Some((array, index_term, element_term)) =
        direct_select_repair_target(arena, failure.conjunct_term)
    else {
        return Ok(Vec::new());
    };
    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext select diagnostic failed: {e}"))
    };
    let current_false = positive_replay_false_count(arena, originals, projected)?;
    let index = eval(arena, index_term, projected).map_err(ir)?;
    let element = eval(arena, element_term, projected).map_err(ir)?;
    let mut diagnostics = Vec::new();

    let mut chain_trial = projected.clone();
    let mut chain_stats = ProjectionRepairStats {
        candidates: 1,
        ..ProjectionRepairStats::default()
    };
    let mut visited = BTreeSet::new();
    if repair_projected_store_chain_readback(
        arena,
        originals,
        &mut chain_trial,
        array,
        &index,
        &element,
        0,
        &mut visited,
        &mut chain_stats,
    )? {
        diagnostics.push(replay_select_candidate_from_trial(
            arena,
            originals,
            failure,
            current_false,
            "chain",
            chain_stats,
            &chain_trial,
        )?);
    } else {
        diagnostics.push(replay_unrepaired_select_candidate("chain", chain_stats));
    }

    let mut direct_trial = projected.clone();
    let mut direct_stats = ProjectionRepairStats {
        candidates: 1,
        ..ProjectionRepairStats::default()
    };
    if store_projected_array_entry(arena, &mut direct_trial, array, index, element)? {
        direct_stats.array_changes += 1;
        diagnostics.push(replay_select_candidate_from_trial(
            arena,
            originals,
            failure,
            current_false,
            "direct",
            direct_stats,
            &direct_trial,
        )?);
    } else {
        diagnostics.push(replay_unrepaired_select_candidate("direct", direct_stats));
    }

    Ok(diagnostics)
}

#[allow(clippy::too_many_arguments)]
fn replay_branch_select_candidate_from_trial(
    arena: &TermArena,
    originals: &[TermId],
    current_false: usize,
    branch_ordinal: usize,
    select_failure: &ReplayFailure,
    kind: &str,
    branch_stats: ProjectionRepairStats,
    select_stats: ProjectionRepairStats,
    trial: &Assignment,
) -> Result<ReplayBranchSelectCandidateDiagnostic, SolverError> {
    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext branch-select diagnostic failed: {e}"))
    };
    let target_true =
        eval(arena, select_failure.conjunct_term, trial).map_err(ir)? == Value::Bool(true);
    let total_false = positive_replay_false_count(arena, originals, trial)?;
    let global_failure =
        first_projected_replay_failure(arena, originals, trial, ProjectionRepairStats::default())?;
    let first_global_false_or = if let Some(or_failure) = global_failure
        .as_ref()
        .and_then(|failure| failure.failed_or.clone())
    {
        Some(enrich_replay_or_failure_with_scalar_choices(
            arena,
            originals,
            trial,
            global_failure
                .as_ref()
                .map_or(select_failure.conjunct_term, |failure| {
                    failure.conjunct_term
                }),
            or_failure,
        )?)
    } else {
        None
    };
    Ok(ReplayBranchSelectCandidateDiagnostic {
        branch_ordinal,
        select_ordinal: select_failure.conjunct_ordinal,
        select_term: select_failure.conjunct_term,
        kind: kind.to_owned(),
        status: select_candidate_status(target_true, total_false, current_false),
        branch_repair_changes: branch_stats.changes(),
        select_repair_changes: select_stats.changes(),
        target_true,
        total_false_conjuncts: Some(total_false),
        first_global_false_ordinal: global_failure
            .as_ref()
            .map(|failure| failure.conjunct_ordinal),
        first_global_false_term: global_failure.as_ref().map(|failure| failure.conjunct_term),
        first_global_false_eq: global_failure.and_then(|failure| failure.failed_eq),
        first_global_false_or,
    })
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn replay_branch_select_residual_candidate_from_trial(
    arena: &TermArena,
    originals: &[TermId],
    branch_disjunction: TermId,
    branches: &[TermId],
    current_false: usize,
    branch_ordinal: usize,
    select_failure: &ReplayFailure,
    kind: &str,
    branch_stats: ProjectionRepairStats,
    select_stats: ProjectionRepairStats,
    trial: &Assignment,
) -> Result<Vec<ReplayBranchSelectCandidateDiagnostic>, SolverError> {
    const MAX_RESIDUAL_FOLLOWUP_OR_DIAGNOSTIC_HOPS: usize = 4;

    let Some(global_failure) =
        first_projected_replay_failure(arena, originals, trial, ProjectionRepairStats::default())?
    else {
        return Ok(Vec::new());
    };
    if global_failure.conjunct_term != branch_disjunction {
        return Ok(Vec::new());
    }
    let Some(or_failure) = global_failure.failed_or else {
        return Ok(Vec::new());
    };
    if or_failure.best_branch_ordinal != branch_ordinal
        || or_failure.best_branch_false_literals != 1
    {
        return Ok(Vec::new());
    }
    let Some(false_literal) = or_failure.best_branch_first_false_term else {
        return Ok(Vec::new());
    };
    let Some(&branch) = branches.get(branch_ordinal) else {
        return Ok(Vec::new());
    };

    let mut residual_trial = trial.clone();
    let mut residual_stats = ProjectionRepairStats::default();
    let residual_kind = if let Some(target) = store_base_repair_target(arena, false_literal) {
        if !repair_projected_store_target_from_current_base(
            arena,
            originals,
            &mut residual_trial,
            target,
            &mut residual_stats,
        )? {
            return Ok(Vec::new());
        }
        "same_branch_store_target"
    } else {
        if !repair_projected_branch_literal_in_branch(
            arena,
            originals,
            branch,
            false_literal,
            &mut residual_trial,
            &mut residual_stats,
        )? {
            return Ok(Vec::new());
        }
        "same_branch_literal"
    };
    let mut combined_select_stats = select_stats;
    combined_select_stats.absorb(residual_stats);
    let residual_kind = format!("{kind}+{residual_kind}");
    let mut diagnostics = vec![replay_branch_select_candidate_from_trial(
        arena,
        originals,
        current_false,
        branch_ordinal,
        select_failure,
        &residual_kind,
        branch_stats,
        combined_select_stats,
        &residual_trial,
    )?];

    let mut followup_trial = residual_trial;
    let mut followup_select_stats = combined_select_stats;
    let mut followup_kind = residual_kind;
    for _ in 0..MAX_RESIDUAL_FOLLOWUP_OR_DIAGNOSTIC_HOPS {
        let Some(followup_failure) = first_projected_replay_failure(
            arena,
            originals,
            &followup_trial,
            ProjectionRepairStats::default(),
        )?
        else {
            break;
        };
        if followup_failure.conjunct_term == branch_disjunction
            || !matches!(
                arena.node(followup_failure.conjunct_term),
                TermNode::App { op: Op::BoolOr, .. }
            )
        {
            break;
        }
        let Some(followup_or) = followup_failure.failed_or else {
            break;
        };
        let mut next_trial = followup_trial.clone();
        let Some((followup_repair_kind, followup_stats)) =
            repair_projected_branch_best_candidate_with_scalar_closure_guard(
                arena,
                originals,
                followup_failure.conjunct_term,
                followup_or.best_branch_term,
                &mut next_trial,
            )?
        else {
            break;
        };
        followup_select_stats.absorb(followup_stats);
        followup_kind = format!(
            "{followup_kind}+followup_or{}_branch{}_{}",
            followup_failure.conjunct_ordinal,
            followup_or.best_branch_ordinal,
            followup_repair_kind
        );
        diagnostics.push(replay_branch_select_candidate_from_trial(
            arena,
            originals,
            current_false,
            branch_ordinal,
            select_failure,
            &followup_kind,
            branch_stats,
            followup_select_stats,
            &next_trial,
        )?);
        followup_trial = next_trial;
    }
    Ok(diagnostics)
}

#[allow(clippy::too_many_lines)]
fn replay_branch_select_candidate_diagnostics(
    arena: &TermArena,
    originals: &[TermId],
    branch_disjunction: TermId,
    projected: &Assignment,
) -> Result<Vec<ReplayBranchSelectCandidateDiagnostic>, SolverError> {
    const MAX_BRANCH_SELECT_DIAGNOSTICS: usize = 16;

    if !matches!(
        arena.node(branch_disjunction),
        TermNode::App { op: Op::BoolOr, .. }
    ) {
        return Ok(Vec::new());
    }

    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext branch-select diagnostic failed: {e}"))
    };
    let current_total_false = positive_replay_false_count(arena, originals, projected)?;
    let mut branches = Vec::new();
    collect_positive_disjuncts(arena, branch_disjunction, &mut branches);
    let mut diagnostics = Vec::new();
    for (branch_ordinal, &branch) in branches.iter().enumerate() {
        let mut branch_trial = projected.clone();
        let Some(branch_stats) =
            repair_projected_branch_as_candidate(arena, originals, branch, &mut branch_trial)?
        else {
            continue;
        };
        if eval(arena, branch_disjunction, &branch_trial).map_err(ir)? != Value::Bool(true) {
            continue;
        }

        let Some(select_failure) = first_projected_replay_failure(
            arena,
            originals,
            &branch_trial,
            ProjectionRepairStats::default(),
        )?
        else {
            continue;
        };
        let Some((array, index_term, element_term)) =
            direct_select_repair_target(arena, select_failure.conjunct_term)
        else {
            continue;
        };

        let index = eval(arena, index_term, &branch_trial).map_err(ir)?;
        let element = eval(arena, element_term, &branch_trial).map_err(ir)?;

        let mut chain_trial = branch_trial.clone();
        let mut chain_stats = ProjectionRepairStats {
            candidates: 1,
            ..ProjectionRepairStats::default()
        };
        let mut visited = BTreeSet::new();
        if repair_projected_store_chain_readback(
            arena,
            originals,
            &mut chain_trial,
            array,
            &index,
            &element,
            0,
            &mut visited,
            &mut chain_stats,
        )? {
            diagnostics.push(replay_branch_select_candidate_from_trial(
                arena,
                originals,
                current_total_false,
                branch_ordinal,
                &select_failure,
                "chain",
                branch_stats,
                chain_stats,
                &chain_trial,
            )?);
            if diagnostics.len() >= MAX_BRANCH_SELECT_DIAGNOSTICS {
                return Ok(diagnostics);
            }
            let residual_diagnostics = replay_branch_select_residual_candidate_from_trial(
                arena,
                originals,
                branch_disjunction,
                &branches,
                current_total_false,
                branch_ordinal,
                &select_failure,
                "chain",
                branch_stats,
                chain_stats,
                &chain_trial,
            )?;
            for diagnostic in residual_diagnostics {
                diagnostics.push(diagnostic);
                if diagnostics.len() >= MAX_BRANCH_SELECT_DIAGNOSTICS {
                    return Ok(diagnostics);
                }
            }
        }

        let mut direct_trial = branch_trial.clone();
        let mut direct_stats = ProjectionRepairStats {
            candidates: 1,
            ..ProjectionRepairStats::default()
        };
        if store_projected_array_entry(arena, &mut direct_trial, array, index, element)? {
            direct_stats.array_changes += 1;
            diagnostics.push(replay_branch_select_candidate_from_trial(
                arena,
                originals,
                current_total_false,
                branch_ordinal,
                &select_failure,
                "direct",
                branch_stats,
                direct_stats,
                &direct_trial,
            )?);
            if diagnostics.len() >= MAX_BRANCH_SELECT_DIAGNOSTICS {
                return Ok(diagnostics);
            }
            let residual_diagnostics = replay_branch_select_residual_candidate_from_trial(
                arena,
                originals,
                branch_disjunction,
                &branches,
                current_total_false,
                branch_ordinal,
                &select_failure,
                "direct",
                branch_stats,
                direct_stats,
                &direct_trial,
            )?;
            for diagnostic in residual_diagnostics {
                diagnostics.push(diagnostic);
                if diagnostics.len() >= MAX_BRANCH_SELECT_DIAGNOSTICS {
                    return Ok(diagnostics);
                }
            }
        }
    }
    Ok(diagnostics)
}

fn replay_failure_with_branch_candidate_diagnostics(
    arena: &TermArena,
    originals: &[TermId],
    projected: &Assignment,
    mut failure: ReplayFailure,
) -> Result<ReplayFailure, SolverError> {
    if let Some(or_failure) = failure.failed_or.take() {
        failure.failed_or = Some(enrich_replay_or_failure_with_scalar_choices(
            arena,
            originals,
            projected,
            failure.conjunct_term,
            or_failure,
        )?);
    }
    failure.select_candidate_diagnostics =
        replay_select_candidate_diagnostics(arena, originals, projected, &failure)?;
    failure.branch_candidate_diagnostics =
        replay_branch_candidate_diagnostics(arena, originals, failure.conjunct_term, projected)?;
    failure.branch_select_candidate_diagnostics = replay_branch_select_candidate_diagnostics(
        arena,
        originals,
        failure.conjunct_term,
        projected,
    )?;
    failure.branch_pair_candidate_diagnostics = replay_branch_pair_candidate_diagnostics(
        arena,
        originals,
        failure.conjunct_term,
        projected,
    )?;
    Ok(failure)
}

#[derive(Clone)]
struct ReplayRepairBeamState {
    assignment: Assignment,
    stats: ProjectionRepairStats,
    false_count: usize,
    depth: usize,
    sequence: usize,
    seen_failures: BTreeMap<usize, usize>,
}

type ReplayRepairBeamSuccess = (usize, usize, usize, ProjectionRepairStats, Assignment);

fn replay_repair_beam_state_key(state: &ReplayRepairBeamState) -> (usize, usize, usize, usize) {
    (
        state.false_count,
        state.depth,
        state.stats.changes(),
        state.sequence,
    )
}

fn replay_repair_beam_success_is_better(
    best: Option<&ReplayRepairBeamSuccess>,
    false_count: usize,
    depth: usize,
    sequence: usize,
) -> bool {
    best.is_none_or(|(best_false_count, best_depth, best_sequence, _, _)| {
        (false_count, depth, sequence) < (*best_false_count, *best_depth, *best_sequence)
    })
}

fn replay_repair_beam_record_success(
    best: &mut Option<ReplayRepairBeamSuccess>,
    false_count: usize,
    depth: usize,
    sequence: usize,
    stats: ProjectionRepairStats,
    assignment: Assignment,
) {
    if replay_repair_beam_success_is_better(best.as_ref(), false_count, depth, sequence) {
        *best = Some((false_count, depth, sequence, stats, assignment));
    }
}

struct ReplayRepairBeamSearch<'a> {
    arena: &'a TermArena,
    originals: &'a [TermId],
    baseline_false: usize,
    max_false: usize,
    max_depth: usize,
}

#[allow(clippy::too_many_arguments)]
fn replay_repair_beam_consider_trial(
    search: &ReplayRepairBeamSearch<'_>,
    trial: Assignment,
    stats: ProjectionRepairStats,
    false_count: usize,
    depth: usize,
    sequence: &mut usize,
    seen_failures: &BTreeMap<usize, usize>,
    frontier: &mut Vec<ReplayRepairBeamState>,
    best: &mut Option<ReplayRepairBeamSuccess>,
) {
    if false_count > search.max_false {
        return;
    }
    if false_count < search.baseline_false {
        replay_repair_beam_record_success(best, false_count, depth, *sequence, stats, trial);
        *sequence += 1;
        return;
    }
    frontier.push(ReplayRepairBeamState {
        assignment: trial,
        stats,
        false_count,
        depth,
        sequence: *sequence,
        seen_failures: seen_failures.clone(),
    });
    *sequence += 1;
}

#[allow(clippy::too_many_arguments)]
fn replay_repair_beam_consider_select_trial(
    search: &ReplayRepairBeamSearch<'_>,
    failure: &ReplayFailure,
    trial: Assignment,
    stats: ProjectionRepairStats,
    depth: usize,
    sequence: &mut usize,
    seen_failures: &BTreeMap<usize, usize>,
    frontier: &mut Vec<ReplayRepairBeamState>,
    best: &mut Option<ReplayRepairBeamSuccess>,
) -> Result<(), SolverError> {
    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext mixed replay repair failed: {e}"))
    };
    if eval(search.arena, failure.conjunct_term, &trial).map_err(ir)? != Value::Bool(true) {
        return Ok(());
    }
    let false_count = positive_replay_false_count(search.arena, search.originals, &trial)?;
    replay_repair_beam_consider_trial(
        search,
        trial,
        stats,
        false_count,
        depth,
        sequence,
        seen_failures,
        frontier,
        best,
    );
    Ok(())
}

fn replay_repair_beam_expand_select(
    search: &ReplayRepairBeamSearch<'_>,
    state: &ReplayRepairBeamState,
    failure: &ReplayFailure,
    seen_failures: &BTreeMap<usize, usize>,
    frontier: &mut Vec<ReplayRepairBeamState>,
    best: &mut Option<ReplayRepairBeamSuccess>,
    sequence: &mut usize,
) -> Result<bool, SolverError> {
    let Some((array, index_term, element_term)) =
        direct_select_repair_target(search.arena, failure.conjunct_term)
    else {
        return Ok(false);
    };
    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext mixed replay repair failed: {e}"))
    };
    let index = eval(search.arena, index_term, &state.assignment).map_err(ir)?;
    let element = eval(search.arena, element_term, &state.assignment).map_err(ir)?;

    let mut chain_trial = state.assignment.clone();
    let mut chain_stats = ProjectionRepairStats {
        candidates: 1,
        ..ProjectionRepairStats::default()
    };
    let mut visited = BTreeSet::new();
    if repair_projected_store_chain_readback(
        search.arena,
        search.originals,
        &mut chain_trial,
        array,
        &index,
        &element,
        0,
        &mut visited,
        &mut chain_stats,
    )? {
        let mut accumulated_stats = state.stats;
        accumulated_stats.absorb(chain_stats);
        replay_repair_beam_consider_select_trial(
            search,
            failure,
            chain_trial,
            accumulated_stats,
            state.depth + 1,
            sequence,
            seen_failures,
            frontier,
            best,
        )?;
    }

    let mut direct_trial = state.assignment.clone();
    let mut direct_stats = ProjectionRepairStats {
        candidates: 1,
        ..ProjectionRepairStats::default()
    };
    if store_projected_array_entry(search.arena, &mut direct_trial, array, index, element)? {
        direct_stats.array_changes += 1;
        let mut accumulated_stats = state.stats;
        accumulated_stats.absorb(direct_stats);
        replay_repair_beam_consider_select_trial(
            search,
            failure,
            direct_trial,
            accumulated_stats,
            state.depth + 1,
            sequence,
            seen_failures,
            frontier,
            best,
        )?;
    }

    Ok(true)
}

#[allow(clippy::too_many_arguments)]
fn replay_repair_beam_expand_branch(
    search: &ReplayRepairBeamSearch<'_>,
    state: &ReplayRepairBeamState,
    failure: &ReplayFailure,
    seen_failures: &BTreeMap<usize, usize>,
    frontier: &mut Vec<ReplayRepairBeamState>,
    best: &mut Option<ReplayRepairBeamSuccess>,
    sequence: &mut usize,
) -> Result<bool, SolverError> {
    if !matches!(
        search.arena.node(failure.conjunct_term),
        TermNode::App { op: Op::BoolOr, .. }
    ) {
        return Ok(false);
    }

    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext mixed replay repair failed: {e}"))
    };
    let branch_search = BranchBeamSearch {
        arena: search.arena,
        originals: search.originals,
        current_false: search.baseline_false,
        max_false: search.max_false,
        max_depth: search.max_depth,
    };
    let mut branches = Vec::new();
    collect_positive_disjuncts(search.arena, failure.conjunct_term, &mut branches);
    for branch in branches {
        let mut trial = state.assignment.clone();
        let Some(branch_stats) = repair_projected_branch_as_candidate(
            search.arena,
            search.originals,
            branch,
            &mut trial,
        )?
        else {
            continue;
        };
        if eval(search.arena, failure.conjunct_term, &trial).map_err(ir)? != Value::Bool(true) {
            continue;
        }
        let (false_count, accumulated_stats, trial) =
            branch_beam_stabilized_candidate(&branch_search, state.stats, branch_stats, trial)?;
        replay_repair_beam_consider_trial(
            search,
            trial,
            accumulated_stats,
            false_count,
            state.depth + 1,
            sequence,
            seen_failures,
            frontier,
            best,
        );
    }

    Ok(true)
}

fn replay_repair_beam_expand_state(
    search: &ReplayRepairBeamSearch<'_>,
    state: ReplayRepairBeamState,
    frontier: &mut Vec<ReplayRepairBeamState>,
    best: &mut Option<ReplayRepairBeamSuccess>,
    sequence: &mut usize,
) -> Result<(), SolverError> {
    const MAX_MIXED_BEAM_FAILURE_VISITS: usize = 2;

    let Some(failure) = first_projected_replay_failure(
        search.arena,
        search.originals,
        &state.assignment,
        ProjectionRepairStats::default(),
    )?
    else {
        replay_repair_beam_record_success(
            best,
            0,
            state.depth,
            state.sequence,
            state.stats,
            state.assignment,
        );
        return Ok(());
    };
    if state.depth >= search.max_depth {
        return Ok(());
    }
    let seen_count = state
        .seen_failures
        .get(&failure.conjunct_ordinal)
        .copied()
        .unwrap_or(0);
    if seen_count >= MAX_MIXED_BEAM_FAILURE_VISITS {
        return Ok(());
    }
    let mut seen_failures = state.seen_failures.clone();
    *seen_failures.entry(failure.conjunct_ordinal).or_default() += 1;

    if replay_repair_beam_expand_select(
        search,
        &state,
        &failure,
        &seen_failures,
        frontier,
        best,
        sequence,
    )? {
        return Ok(());
    }
    let _ = replay_repair_beam_expand_branch(
        search,
        &state,
        &failure,
        &seen_failures,
        frontier,
        best,
        sequence,
    )?;
    Ok(())
}

fn repair_projected_replay_mixed_beam(
    arena: &TermArena,
    originals: &[TermId],
    projected: &Assignment,
    baseline_false: usize,
) -> Result<Option<(ProjectionRepairStats, Assignment)>, SolverError> {
    const MAX_MIXED_REPAIR_BEAM_DEPTH: usize = 6;
    const MAX_MIXED_REPAIR_BEAM_WIDTH: usize = 8;
    const MAX_MIXED_REPAIR_BEAM_EXPANSIONS: usize = 64;
    const MAX_MIXED_REPAIR_BEAM_UPHILL_FALSE: usize = 4;

    if baseline_false == 0 {
        return Ok(None);
    }
    let search = ReplayRepairBeamSearch {
        arena,
        originals,
        baseline_false,
        max_false: baseline_false + MAX_MIXED_REPAIR_BEAM_UPHILL_FALSE,
        max_depth: MAX_MIXED_REPAIR_BEAM_DEPTH,
    };
    let mut sequence = 1usize;
    let mut expansions = 0usize;
    let mut best: Option<ReplayRepairBeamSuccess> = None;
    let mut frontier = vec![ReplayRepairBeamState {
        assignment: projected.clone(),
        stats: ProjectionRepairStats::default(),
        false_count: baseline_false,
        depth: 0,
        sequence: 0,
        seen_failures: BTreeMap::new(),
    }];

    while !frontier.is_empty() && expansions < MAX_MIXED_REPAIR_BEAM_EXPANSIONS {
        frontier.sort_by_key(replay_repair_beam_state_key);
        let state = frontier.remove(0);
        expansions += 1;
        replay_repair_beam_expand_state(&search, state, &mut frontier, &mut best, &mut sequence)?;
        frontier.sort_by_key(replay_repair_beam_state_key);
        frontier.truncate(MAX_MIXED_REPAIR_BEAM_WIDTH);
    }

    let Some((_, _, _, stats, trial)) = best else {
        return Ok(None);
    };
    Ok(Some((stats, trial)))
}

fn repair_projected_replay_select_failure(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
    failure: &ReplayFailure,
) -> Result<Option<ProjectionRepairStats>, SolverError> {
    let Some((array, index_term, element_term)) =
        direct_select_repair_target(arena, failure.conjunct_term)
    else {
        return Ok(None);
    };
    let ir =
        |e: axeyum_ir::IrError| SolverError::Backend(format!("lazy-ext select repair failed: {e}"));
    let current_false = positive_replay_false_count(arena, originals, projected)?;
    let index = eval(arena, index_term, projected).map_err(ir)?;
    let element = eval(arena, element_term, projected).map_err(ir)?;
    let mut best: Option<(usize, usize, ProjectionRepairStats, Assignment)> = None;

    if let Some((stats, trial)) =
        repair_projected_replay_mixed_beam(arena, originals, projected, current_false)?
    {
        *projected = trial;
        return Ok(Some(stats));
    }

    let mut consider = |ordinal: usize,
                        trial: Assignment,
                        stats: ProjectionRepairStats|
     -> Result<(), SolverError> {
        if eval(arena, failure.conjunct_term, &trial).map_err(ir)? != Value::Bool(true) {
            return Ok(());
        }
        let total_false = positive_replay_false_count(arena, originals, &trial)?;
        if total_false > current_false {
            return Ok(());
        }
        let replace = best
            .as_ref()
            .is_none_or(|(best_total_false, best_ordinal, _, _)| {
                (total_false, ordinal) < (*best_total_false, *best_ordinal)
            });
        if replace {
            best = Some((total_false, ordinal, stats, trial));
        }
        Ok(())
    };

    let mut chain_trial = projected.clone();
    let mut chain_stats = ProjectionRepairStats {
        candidates: 1,
        ..ProjectionRepairStats::default()
    };
    let mut visited = BTreeSet::new();
    if repair_projected_store_chain_readback(
        arena,
        originals,
        &mut chain_trial,
        array,
        &index,
        &element,
        0,
        &mut visited,
        &mut chain_stats,
    )? {
        consider(0, chain_trial, chain_stats)?;
    }

    let mut direct_trial = projected.clone();
    let mut direct_stats = ProjectionRepairStats {
        candidates: 1,
        ..ProjectionRepairStats::default()
    };
    if store_projected_array_entry(
        arena,
        &mut direct_trial,
        array,
        index.clone(),
        element.clone(),
    )? {
        direct_stats.array_changes += 1;
        consider(1, direct_trial, direct_stats)?;
    }

    let Some((_, _, stats, trial)) = best else {
        return Ok(None);
    };
    *projected = trial;
    Ok(Some(stats))
}

type BranchSelectCycleRepairChoice = (
    usize,
    usize,
    usize,
    usize,
    ProjectionRepairStats,
    Assignment,
);

fn branch_select_cycle_choice_is_better(
    best: Option<&BranchSelectCycleRepairChoice>,
    total_false: usize,
    first_ordinal: usize,
    select_ordinal: usize,
    second_ordinal: usize,
) -> bool {
    best.is_none_or(
        |(best_total_false, best_first_ordinal, best_select_ordinal, best_second_ordinal, _, _)| {
            (total_false, first_ordinal, select_ordinal, second_ordinal)
                < (
                    *best_total_false,
                    *best_first_ordinal,
                    *best_select_ordinal,
                    *best_second_ordinal,
                )
        },
    )
}

#[allow(clippy::too_many_arguments)]
fn repair_projected_replay_branch_select_residual_chain(
    search: &BranchSelectCycleSearch<'_>,
    first_ordinal: usize,
    select_ordinal: usize,
    select_failure: &ReplayFailure,
    mut stats: ProjectionRepairStats,
    mut trial: Assignment,
    best: &mut Option<BranchSelectCycleRepairChoice>,
) -> Result<(), SolverError> {
    const MAX_BRANCH_SELECT_RESIDUAL_CHAIN_HOPS: usize = 4;

    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!(
            "lazy-ext branch-select residual repair failed: {e}"
        ))
    };
    for _ in 0..=MAX_BRANCH_SELECT_RESIDUAL_CHAIN_HOPS {
        if eval(search.arena, search.branch_disjunction, &trial).map_err(ir)? != Value::Bool(true)
            || eval(search.arena, select_failure.conjunct_term, &trial).map_err(ir)?
                != Value::Bool(true)
        {
            return Ok(());
        }

        let total_false = positive_replay_false_count(search.arena, search.originals, &trial)?;
        if total_false < search.current_false
            && branch_select_cycle_choice_is_better(
                best.as_ref(),
                total_false,
                first_ordinal,
                select_ordinal,
                first_ordinal,
            )
        {
            *best = Some((
                total_false,
                first_ordinal,
                select_ordinal,
                first_ordinal,
                stats,
                trial.clone(),
            ));
        }
        if total_false == 0 {
            return Ok(());
        }

        let Some(followup_failure) = first_projected_replay_failure(
            search.arena,
            search.originals,
            &trial,
            ProjectionRepairStats::default(),
        )?
        else {
            return Ok(());
        };
        if followup_failure.conjunct_term == search.branch_disjunction
            || !matches!(
                search.arena.node(followup_failure.conjunct_term),
                TermNode::App { op: Op::BoolOr, .. }
            )
        {
            return Ok(());
        }
        let Some(followup_or) = followup_failure.failed_or else {
            return Ok(());
        };

        let mut followup_trial = trial.clone();
        let Some((_, followup_stats)) =
            repair_projected_branch_best_candidate_with_scalar_closure_guard(
                search.arena,
                search.originals,
                followup_failure.conjunct_term,
                followup_or.best_branch_term,
                &mut followup_trial,
            )?
        else {
            return Ok(());
        };
        if eval(
            search.arena,
            followup_failure.conjunct_term,
            &followup_trial,
        )
        .map_err(ir)?
            != Value::Bool(true)
            || eval(search.arena, search.branch_disjunction, &followup_trial).map_err(ir)?
                != Value::Bool(true)
            || eval(search.arena, select_failure.conjunct_term, &followup_trial).map_err(ir)?
                != Value::Bool(true)
        {
            return Ok(());
        }
        stats.absorb(followup_stats);
        trial = followup_trial;
    }
    Ok(())
}

struct BranchSelectCycleSearch<'a> {
    arena: &'a TermArena,
    originals: &'a [TermId],
    branch_disjunction: TermId,
    branches: &'a [TermId],
    current_false: usize,
    allow_alternate_branches: bool,
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn repair_projected_replay_branch_select_cycle_after_select(
    search: &BranchSelectCycleSearch<'_>,
    first_ordinal: usize,
    first_stats: ProjectionRepairStats,
    select_ordinal: usize,
    select_failure: &ReplayFailure,
    select_stats: ProjectionRepairStats,
    select_trial: &Assignment,
    trials: &mut usize,
    best: &mut Option<BranchSelectCycleRepairChoice>,
) -> Result<(), SolverError> {
    const MAX_BRANCH_SELECT_CYCLE_TRIALS: usize = 32;

    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext branch-select cycle repair failed: {e}"))
    };
    if eval(search.arena, select_failure.conjunct_term, select_trial).map_err(ir)?
        != Value::Bool(true)
    {
        return Ok(());
    }
    let Some(cycle_failure) = first_projected_replay_failure(
        search.arena,
        search.originals,
        select_trial,
        ProjectionRepairStats::default(),
    )?
    else {
        return Ok(());
    };
    if cycle_failure.conjunct_term != search.branch_disjunction {
        return Ok(());
    }

    let branch_search = BranchBeamSearch {
        arena: search.arena,
        originals: search.originals,
        current_false: search.current_false,
        max_false: search.current_false + 4,
        max_depth: 2,
    };
    let mut prefix_stats = first_stats;
    prefix_stats.absorb(select_stats);

    if let Some(or_failure) = &cycle_failure.failed_or
        && or_failure.best_branch_ordinal == first_ordinal
        && or_failure.best_branch_false_literals == 1
        && let Some(false_literal) = or_failure.best_branch_first_false_term
    {
        let mut residual_trial = select_trial.clone();
        let mut residual_stats = prefix_stats;
        let repaired = if let Some(target) = store_base_repair_target(search.arena, false_literal) {
            repair_projected_store_target_from_current_base(
                search.arena,
                search.originals,
                &mut residual_trial,
                target,
                &mut residual_stats,
            )?
        } else {
            repair_projected_branch_literal_in_branch(
                search.arena,
                search.originals,
                search.branches[first_ordinal],
                false_literal,
                &mut residual_trial,
                &mut residual_stats,
            )?
        };
        if repaired
            && eval(search.arena, search.branch_disjunction, &residual_trial).map_err(ir)?
                == Value::Bool(true)
            && eval(search.arena, select_failure.conjunct_term, &residual_trial).map_err(ir)?
                == Value::Bool(true)
        {
            repair_projected_replay_branch_select_residual_chain(
                search,
                first_ordinal,
                select_ordinal,
                select_failure,
                residual_stats,
                residual_trial,
                best,
            )?;
        }
    }

    if !search.allow_alternate_branches {
        return Ok(());
    }

    for (second_ordinal, &second_branch) in search.branches.iter().enumerate() {
        if second_ordinal == first_ordinal {
            continue;
        }
        if *trials >= MAX_BRANCH_SELECT_CYCLE_TRIALS {
            return Ok(());
        }
        *trials += 1;

        let mut second_trial = select_trial.clone();
        let Some(second_stats) = repair_projected_branch_as_candidate(
            search.arena,
            search.originals,
            second_branch,
            &mut second_trial,
        )?
        else {
            continue;
        };
        if eval(search.arena, search.branch_disjunction, &second_trial).map_err(ir)?
            != Value::Bool(true)
            || eval(search.arena, select_failure.conjunct_term, &second_trial).map_err(ir)?
                != Value::Bool(true)
        {
            continue;
        }

        let (total_false, stats, trial) = branch_beam_stabilized_candidate(
            &branch_search,
            prefix_stats,
            second_stats,
            second_trial,
        )?;
        if total_false >= search.current_false
            || eval(search.arena, search.branch_disjunction, &trial).map_err(ir)?
                != Value::Bool(true)
            || eval(search.arena, select_failure.conjunct_term, &trial).map_err(ir)?
                != Value::Bool(true)
        {
            continue;
        }
        if branch_select_cycle_choice_is_better(
            best.as_ref(),
            total_false,
            first_ordinal,
            select_ordinal,
            second_ordinal,
        ) {
            *best = Some((
                total_false,
                first_ordinal,
                select_ordinal,
                second_ordinal,
                stats,
                trial,
            ));
        }
    }
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn repair_projected_replay_branch_select_cycle(
    arena: &TermArena,
    originals: &[TermId],
    branch_disjunction: TermId,
    projected: &mut Assignment,
) -> Result<Option<ProjectionRepairStats>, SolverError> {
    const MAX_BRANCH_SELECT_CYCLE_BRANCHES: usize = 8;
    const MAX_BRANCH_SELECT_CYCLE_CONJUNCTS: usize = 64;

    if !matches!(
        arena.node(branch_disjunction),
        TermNode::App { op: Op::BoolOr, .. }
    ) {
        return Ok(None);
    }

    let current_false = positive_replay_false_count(arena, originals, projected)?;
    if current_false == 0
        || current_false > 2
        || positive_replay_conjunct_count(arena, originals) > MAX_BRANCH_SELECT_CYCLE_CONJUNCTS
    {
        return Ok(None);
    }
    let allow_alternate_branches = true;

    let ir = |e: axeyum_ir::IrError| {
        SolverError::Backend(format!("lazy-ext branch-select cycle repair failed: {e}"))
    };
    let mut branches = Vec::new();
    collect_positive_disjuncts(arena, branch_disjunction, &mut branches);
    branches.truncate(MAX_BRANCH_SELECT_CYCLE_BRANCHES);
    if branches.len() < 2 {
        return Ok(None);
    }

    let search = BranchSelectCycleSearch {
        arena,
        originals,
        branch_disjunction,
        branches: &branches,
        current_false,
        allow_alternate_branches,
    };
    let mut trials = 0usize;
    let mut best: Option<BranchSelectCycleRepairChoice> = None;

    for (first_ordinal, &first_branch) in branches.iter().enumerate() {
        let mut branch_trial = projected.clone();
        let Some(first_stats) = repair_projected_branch_as_candidate(
            arena,
            originals,
            first_branch,
            &mut branch_trial,
        )?
        else {
            continue;
        };
        if eval(arena, branch_disjunction, &branch_trial).map_err(ir)? != Value::Bool(true) {
            continue;
        }

        let Some(select_failure) = first_projected_replay_failure(
            arena,
            originals,
            &branch_trial,
            ProjectionRepairStats::default(),
        )?
        else {
            continue;
        };
        let Some((array, index_term, element_term)) =
            direct_select_repair_target(arena, select_failure.conjunct_term)
        else {
            continue;
        };
        let index = eval(arena, index_term, &branch_trial).map_err(ir)?;
        let element = eval(arena, element_term, &branch_trial).map_err(ir)?;

        let mut chain_trial = branch_trial.clone();
        let mut chain_stats = ProjectionRepairStats {
            candidates: 1,
            ..ProjectionRepairStats::default()
        };
        let mut visited = BTreeSet::new();
        if repair_projected_store_chain_readback(
            arena,
            originals,
            &mut chain_trial,
            array,
            &index,
            &element,
            0,
            &mut visited,
            &mut chain_stats,
        )? {
            repair_projected_replay_branch_select_cycle_after_select(
                &search,
                first_ordinal,
                first_stats,
                0,
                &select_failure,
                chain_stats,
                &chain_trial,
                &mut trials,
                &mut best,
            )?;
        }

        let mut direct_trial = branch_trial.clone();
        let mut direct_stats = ProjectionRepairStats {
            candidates: 1,
            ..ProjectionRepairStats::default()
        };
        if store_projected_array_entry(arena, &mut direct_trial, array, index, element)? {
            direct_stats.array_changes += 1;
            repair_projected_replay_branch_select_cycle_after_select(
                &search,
                first_ordinal,
                first_stats,
                1,
                &select_failure,
                direct_stats,
                &direct_trial,
                &mut trials,
                &mut best,
            )?;
        }
    }

    let Some((_, _, _, _, stats, trial)) = best else {
        return Ok(None);
    };
    *projected = trial;
    Ok(Some(stats))
}

fn positive_replay_conjunct_count(arena: &TermArena, originals: &[TermId]) -> usize {
    let mut count = 0;
    let mut conjuncts = Vec::new();
    for &assertion in originals {
        conjuncts.clear();
        collect_positive_conjuncts(arena, assertion, &mut conjuncts);
        count += conjuncts.len();
    }
    count
}

fn mixed_replay_beam_admits_or_failure(
    arena: &TermArena,
    originals: &[TermId],
    current_false: usize,
) -> bool {
    const MAX_OR_MIXED_BEAM_CONJUNCTS: usize = 64;

    current_false > 1
        && positive_replay_conjunct_count(arena, originals) <= MAX_OR_MIXED_BEAM_CONJUNCTS
}

fn repair_projected_replay_failure(
    arena: &TermArena,
    originals: &[TermId],
    projected: &mut Assignment,
    failure: &ReplayFailure,
) -> Result<Option<ProjectionRepairStats>, SolverError> {
    if let Some(select_stats) =
        repair_projected_replay_select_failure(arena, originals, projected, failure)?
    {
        return Ok(Some(select_stats));
    }

    let Some(or_failure) = &failure.failed_or else {
        return Ok(None);
    };

    if let Some(pair_stats) = repair_projected_replay_branch_pair_choice(
        arena,
        originals,
        failure.conjunct_term,
        projected,
    )? {
        return Ok(Some(pair_stats));
    }

    if let Some(beam_stats) =
        repair_projected_replay_branch_beam(arena, originals, failure.conjunct_term, projected)?
    {
        return Ok(Some(beam_stats));
    }

    if let Some(cycle_stats) = repair_projected_replay_branch_select_cycle(
        arena,
        originals,
        failure.conjunct_term,
        projected,
    )? {
        return Ok(Some(cycle_stats));
    }

    let current_false = positive_replay_false_count(arena, originals, projected)?;
    if mixed_replay_beam_admits_or_failure(arena, originals, current_false) {
        if let Some((mixed_stats, trial)) =
            repair_projected_replay_mixed_beam(arena, originals, projected, current_false)?
        {
            *projected = trial;
            return Ok(Some(mixed_stats));
        }
    }

    if let Some(choice_stats) =
        repair_projected_replay_branch_choice(arena, originals, failure.conjunct_term, projected)?
    {
        return Ok(Some(choice_stats));
    }

    if let Some(schedule_stats) =
        repair_projected_branch_schedule(arena, originals, or_failure.best_branch_term, projected)?
    {
        return Ok(Some(schedule_stats));
    }

    if or_failure.best_branch_false_literals != 1 {
        return Ok(None);
    }
    let Some(false_literal) = or_failure.best_branch_first_false_term else {
        return Ok(None);
    };

    let mut stats = ProjectionRepairStats::default();
    let changed = repair_projected_branch_literal_in_branch(
        arena,
        originals,
        or_failure.best_branch_term,
        false_literal,
        projected,
        &mut stats,
    )?;
    Ok(changed.then_some(stats))
}

#[derive(Clone)]
struct BranchBeamState {
    assignment: Assignment,
    stats: ProjectionRepairStats,
    false_count: usize,
    depth: usize,
    sequence: usize,
    seen_failures: BTreeSet<usize>,
}

type BranchBeamSuccess = (usize, usize, usize, ProjectionRepairStats, Assignment);

fn branch_beam_state_key(state: &BranchBeamState) -> (usize, usize, usize, usize) {
    (
        state.false_count,
        state.depth,
        state.stats.changes(),
        state.sequence,
    )
}

fn branch_beam_success_is_better(
    best: Option<&BranchBeamSuccess>,
    false_count: usize,
    depth: usize,
    sequence: usize,
) -> bool {
    best.is_none_or(|(best_false_count, best_depth, best_sequence, _, _)| {
        (false_count, depth, sequence) < (*best_false_count, *best_depth, *best_sequence)
    })
}

fn branch_beam_record_success(
    best: &mut Option<BranchBeamSuccess>,
    false_count: usize,
    depth: usize,
    sequence: usize,
    stats: ProjectionRepairStats,
    assignment: Assignment,
) {
    if branch_beam_success_is_better(best.as_ref(), false_count, depth, sequence) {
        *best = Some((false_count, depth, sequence, stats, assignment));
    }
}

struct BranchBeamSearch<'a> {
    arena: &'a TermArena,
    originals: &'a [TermId],
    current_false: usize,
    max_false: usize,
    max_depth: usize,
}

fn branch_beam_stabilized_candidate(
    search: &BranchBeamSearch<'_>,
    state_stats: ProjectionRepairStats,
    branch_stats: ProjectionRepairStats,
    trial: Assignment,
) -> Result<(usize, ProjectionRepairStats, Assignment), SolverError> {
    let mut raw_stats = state_stats;
    raw_stats.absorb(branch_stats);
    let raw_false = positive_replay_false_count(search.arena, search.originals, &trial)?;

    let mut stabilized = trial.clone();
    let mut stabilized_stats = raw_stats;
    let readback_changes =
        align_all_direct_select_symbols(search.arena, search.originals, &mut stabilized)?;
    stabilized_stats.symbol_changes += readback_changes;
    let stabilized_false =
        positive_replay_false_count(search.arena, search.originals, &stabilized)?;

    if stabilized_false < raw_false {
        Ok((stabilized_false, stabilized_stats, stabilized))
    } else {
        Ok((raw_false, raw_stats, trial))
    }
}

fn branch_beam_expand_state(
    search: &BranchBeamSearch<'_>,
    state: BranchBeamState,
    frontier: &mut Vec<BranchBeamState>,
    best: &mut Option<BranchBeamSuccess>,
    sequence: &mut usize,
) -> Result<(), SolverError> {
    let Some(failure) = first_projected_replay_failure(
        search.arena,
        search.originals,
        &state.assignment,
        ProjectionRepairStats::default(),
    )?
    else {
        branch_beam_record_success(
            best,
            0,
            state.depth,
            state.sequence,
            state.stats,
            state.assignment,
        );
        return Ok(());
    };
    if state.depth >= search.max_depth
        || state.seen_failures.contains(&failure.conjunct_ordinal)
        || !matches!(
            search.arena.node(failure.conjunct_term),
            TermNode::App { op: Op::BoolOr, .. }
        )
    {
        return Ok(());
    }

    let ir =
        |e: axeyum_ir::IrError| SolverError::Backend(format!("lazy-ext branch beam failed: {e}"));
    let mut seen = state.seen_failures.clone();
    seen.insert(failure.conjunct_ordinal);
    let mut branches = Vec::new();
    collect_positive_disjuncts(search.arena, failure.conjunct_term, &mut branches);
    for branch in branches {
        let mut trial = state.assignment.clone();
        let Some(branch_stats) = repair_projected_branch_as_candidate(
            search.arena,
            search.originals,
            branch,
            &mut trial,
        )?
        else {
            continue;
        };
        if eval(search.arena, failure.conjunct_term, &trial).map_err(ir)? != Value::Bool(true) {
            continue;
        }
        let (false_count, accumulated_stats, trial) =
            branch_beam_stabilized_candidate(search, state.stats, branch_stats, trial)?;
        if false_count > search.max_false {
            continue;
        }
        if false_count < search.current_false {
            branch_beam_record_success(
                best,
                false_count,
                state.depth + 1,
                *sequence,
                accumulated_stats,
                trial,
            );
            *sequence += 1;
            continue;
        }
        let next_failure = first_projected_replay_failure(
            search.arena,
            search.originals,
            &trial,
            ProjectionRepairStats::default(),
        )?;
        if next_failure
            .as_ref()
            .is_some_and(|next| seen.contains(&next.conjunct_ordinal))
        {
            continue;
        }
        frontier.push(BranchBeamState {
            assignment: trial,
            stats: accumulated_stats,
            false_count,
            depth: state.depth + 1,
            sequence: *sequence,
            seen_failures: seen.clone(),
        });
        *sequence += 1;
    }
    Ok(())
}

fn repair_projected_replay_branch_beam(
    arena: &TermArena,
    originals: &[TermId],
    branch_disjunction: TermId,
    projected: &mut Assignment,
) -> Result<Option<ProjectionRepairStats>, SolverError> {
    const MAX_BRANCH_BEAM_DEPTH: usize = 6;
    const MAX_BRANCH_BEAM_WIDTH: usize = 8;
    const MAX_BRANCH_BEAM_EXPANSIONS: usize = 64;
    const MAX_BRANCH_BEAM_UPHILL_FALSE: usize = 4;

    if !matches!(
        arena.node(branch_disjunction),
        TermNode::App { op: Op::BoolOr, .. }
    ) {
        return Ok(None);
    }

    let current_false = positive_replay_false_count(arena, originals, projected)?;
    if current_false == 0 {
        return Ok(None);
    }
    let search = BranchBeamSearch {
        arena,
        originals,
        current_false,
        max_false: current_false + MAX_BRANCH_BEAM_UPHILL_FALSE,
        max_depth: MAX_BRANCH_BEAM_DEPTH,
    };
    let mut sequence = 1usize;
    let mut expansions = 0usize;
    let mut best: Option<BranchBeamSuccess> = None;
    let mut frontier = vec![BranchBeamState {
        assignment: projected.clone(),
        stats: ProjectionRepairStats::default(),
        false_count: current_false,
        depth: 0,
        sequence: 0,
        seen_failures: BTreeSet::new(),
    }];

    while !frontier.is_empty() && expansions < MAX_BRANCH_BEAM_EXPANSIONS {
        frontier.sort_by_key(branch_beam_state_key);
        let state = frontier.remove(0);
        expansions += 1;
        branch_beam_expand_state(&search, state, &mut frontier, &mut best, &mut sequence)?;
        frontier.sort_by_key(branch_beam_state_key);
        frontier.truncate(MAX_BRANCH_BEAM_WIDTH);
    }

    let Some((_, _, _, stats, trial)) = best else {
        return Ok(None);
    };
    *projected = trial;
    Ok(Some(stats))
}

type BranchPairRepairChoice = (
    usize,
    usize,
    usize,
    usize,
    ProjectionRepairStats,
    Assignment,
);

fn branch_pair_choice_is_better(
    best: Option<&BranchPairRepairChoice>,
    total_false: usize,
    pair_branch_false: usize,
    first_ordinal: usize,
    second_ordinal: usize,
) -> bool {
    best.is_none_or(
        |(
            best_total_false,
            best_pair_branch_false,
            best_first_ordinal,
            best_second_ordinal,
            _,
            _,
        )| {
            (
                total_false,
                pair_branch_false,
                first_ordinal,
                second_ordinal,
            ) < (
                *best_total_false,
                *best_pair_branch_false,
                *best_first_ordinal,
                *best_second_ordinal,
            )
        },
    )
}

fn repair_projected_replay_branch_pair_choice(
    arena: &TermArena,
    originals: &[TermId],
    branch_disjunction: TermId,
    projected: &mut Assignment,
) -> Result<Option<ProjectionRepairStats>, SolverError> {
    if !matches!(
        arena.node(branch_disjunction),
        TermNode::App { op: Op::BoolOr, .. }
    ) {
        return Ok(None);
    }

    let ir =
        |e: axeyum_ir::IrError| SolverError::Backend(format!("lazy-ext branch repair failed: {e}"));
    let current_false = positive_replay_false_count(arena, originals, projected)?;
    let mut first_branches = Vec::new();
    collect_positive_disjuncts(arena, branch_disjunction, &mut first_branches);
    let mut best: Option<BranchPairRepairChoice> = None;

    for (first_ordinal, first_branch) in first_branches.iter().copied().enumerate() {
        let mut first_trial = projected.clone();
        let Some(first_stats) =
            repair_projected_branch_as_candidate(arena, originals, first_branch, &mut first_trial)?
        else {
            continue;
        };

        let Some(next_failure) = first_projected_replay_failure(
            arena,
            originals,
            &first_trial,
            ProjectionRepairStats::default(),
        )?
        else {
            continue;
        };

        if next_failure.conjunct_term == branch_disjunction
            || !matches!(
                arena.node(next_failure.conjunct_term),
                TermNode::App { op: Op::BoolOr, .. }
            )
        {
            continue;
        }

        let mut second_branches = Vec::new();
        collect_positive_disjuncts(arena, next_failure.conjunct_term, &mut second_branches);
        for (second_ordinal, second_branch) in second_branches.iter().copied().enumerate() {
            let mut pair_trial = first_trial.clone();
            let Some(second_stats) = repair_projected_branch_as_candidate(
                arena,
                originals,
                second_branch,
                &mut pair_trial,
            )?
            else {
                continue;
            };
            if eval(arena, branch_disjunction, &pair_trial).map_err(ir)? != Value::Bool(true)
                || eval(arena, next_failure.conjunct_term, &pair_trial).map_err(ir)?
                    != Value::Bool(true)
            {
                continue;
            }
            let total_false = positive_replay_false_count(arena, originals, &pair_trial)?;
            if total_false >= current_false {
                continue;
            }
            let first_branch_false = branch_false_literal_count(arena, first_branch, &pair_trial)?;
            let second_branch_false =
                branch_false_literal_count(arena, second_branch, &pair_trial)?;
            let pair_branch_false = first_branch_false + second_branch_false;
            if branch_pair_choice_is_better(
                best.as_ref(),
                total_false,
                pair_branch_false,
                first_ordinal,
                second_ordinal,
            ) {
                let mut pair_stats = first_stats;
                pair_stats.absorb(second_stats);
                best = Some((
                    total_false,
                    pair_branch_false,
                    first_ordinal,
                    second_ordinal,
                    pair_stats,
                    pair_trial,
                ));
            }
        }
    }

    let Some((_, _, _, _, stats, trial)) = best else {
        return Ok(None);
    };
    *projected = trial;
    Ok(Some(stats))
}

fn repair_projected_replay_branch_choice(
    arena: &TermArena,
    originals: &[TermId],
    branch_disjunction: TermId,
    projected: &mut Assignment,
) -> Result<Option<ProjectionRepairStats>, SolverError> {
    if !matches!(
        arena.node(branch_disjunction),
        TermNode::App { op: Op::BoolOr, .. }
    ) {
        return Ok(None);
    }

    let current_false = positive_replay_false_count(arena, originals, projected)?;
    let mut branches = Vec::new();
    collect_positive_disjuncts(arena, branch_disjunction, &mut branches);
    let mut best: Option<(usize, usize, usize, ProjectionRepairStats, Assignment)> = None;

    for (ordinal, branch) in branches.iter().copied().enumerate() {
        let mut trial = projected.clone();
        let Some(stats) =
            repair_projected_branch_as_candidate(arena, originals, branch, &mut trial)?
        else {
            continue;
        };
        let total_false = positive_replay_false_count(arena, originals, &trial)?;
        if total_false > current_false {
            continue;
        }
        let branch_false = branch_false_literal_count(arena, branch, &trial)?;
        let replace = best.as_ref().is_none_or(
            |(best_total_false, best_branch_false, best_ordinal, _, _)| {
                (total_false, branch_false, ordinal)
                    < (*best_total_false, *best_branch_false, *best_ordinal)
            },
        );
        if replace {
            best = Some((total_false, branch_false, ordinal, stats, trial));
        }
    }

    let Some((_, _, _, stats, trial)) = best else {
        return Ok(None);
    };
    *projected = trial;
    Ok(Some(stats))
}

fn repair_projected_branch_as_candidate(
    arena: &TermArena,
    originals: &[TermId],
    branch: TermId,
    projected: &mut Assignment,
) -> Result<Option<ProjectionRepairStats>, SolverError> {
    let ir =
        |e: axeyum_ir::IrError| SolverError::Backend(format!("lazy-ext branch repair failed: {e}"));
    let initial_false = branch_false_literal_count(arena, branch, projected)?;
    if initial_false == 0 {
        return Ok(None);
    }

    let mut stats = ProjectionRepairStats::default();
    let mut changed = false;
    let mut literals = Vec::new();
    collect_positive_conjuncts(arena, branch, &mut literals);

    for _ in 0..=2 {
        let mut pass_changes = 0;
        for &literal in &literals {
            if eval(arena, literal, projected).map_err(ir)? == Value::Bool(true) {
                continue;
            }
            if repair_projected_branch_scalar_equality_literal(
                arena, literal, projected, &mut stats,
            )? {
                pass_changes += 1;
                changed = true;
            }
        }
        if pass_changes == 0 {
            break;
        }
    }

    for _ in 0..=2 {
        let mut pass_changes = 0;
        for &literal in &literals {
            if eval(arena, literal, projected).map_err(ir)? == Value::Bool(true) {
                continue;
            }
            if repair_projected_branch_scalar_equality_literal(
                arena, literal, projected, &mut stats,
            )? {
                pass_changes += 1;
                changed = true;
                continue;
            }
            let before = stats.changes();
            if repair_projected_branch_literal_in_branch(
                arena, originals, branch, literal, projected, &mut stats,
            )? {
                pass_changes += stats.changes().saturating_sub(before).max(1);
                changed = true;
            }
        }
        if pass_changes == 0 {
            break;
        }
    }

    let final_false = branch_false_literal_count(arena, branch, projected)?;
    if changed && final_false < initial_false {
        Ok(Some(stats))
    } else {
        Ok(None)
    }
}

fn repair_projected_branch_best_candidate(
    arena: &TermArena,
    originals: &[TermId],
    branch: TermId,
    projected: &mut Assignment,
) -> Result<Option<(&'static str, ProjectionRepairStats)>, SolverError> {
    let mut best: Option<(
        usize,
        usize,
        &'static str,
        ProjectionRepairStats,
        Assignment,
    )> = None;

    let mut greedy_trial = projected.clone();
    if let Some(stats) =
        repair_projected_branch_as_candidate(arena, originals, branch, &mut greedy_trial)?
    {
        let total_false = positive_replay_false_count(arena, originals, &greedy_trial)?;
        best = Some((total_false, stats.changes(), "branch", stats, greedy_trial));
    }

    let mut scalar_trial = projected.clone();
    if let Some(stats) = repair_projected_branch_scalar_choice_candidate(
        arena,
        originals,
        branch,
        &mut scalar_trial,
    )? {
        let total_false = positive_replay_false_count(arena, originals, &scalar_trial)?;
        let replace = best
            .as_ref()
            .is_none_or(|(best_false, best_changes, best_kind, _, _)| {
                (total_false, stats.changes(), "scalar") < (*best_false, *best_changes, *best_kind)
            });
        if replace {
            best = Some((total_false, stats.changes(), "scalar", stats, scalar_trial));
        }
    }

    let Some((_, _, kind, stats, trial)) = best else {
        return Ok(None);
    };
    *projected = trial;
    Ok(Some((kind, stats)))
}

fn scalar_closure_rejects_branch_candidate(
    arena: &TermArena,
    originals: &[TermId],
    disjunction: TermId,
    branch: TermId,
    baseline_false: usize,
    candidate: &Assignment,
) -> Result<bool, SolverError> {
    let (closure_steps, closure_trial) =
        replay_scalar_closure_from_trial(arena, originals, branch, candidate)?;
    if closure_steps.is_empty() {
        return Ok(false);
    }
    let final_total_false = positive_replay_false_count(arena, originals, &closure_trial)?;
    if final_total_false < baseline_false {
        return Ok(false);
    }
    let Some(final_failure) = first_projected_replay_failure(
        arena,
        originals,
        &closure_trial,
        ProjectionRepairStats::default(),
    )?
    else {
        return Ok(false);
    };
    if final_failure.conjunct_term != disjunction {
        return Ok(false);
    }
    Ok(branch_false_literal_count(arena, branch, &closure_trial)? > 0)
}

fn repair_projected_branch_best_candidate_with_scalar_closure_guard(
    arena: &TermArena,
    originals: &[TermId],
    disjunction: TermId,
    branch: TermId,
    projected: &mut Assignment,
) -> Result<Option<(&'static str, ProjectionRepairStats)>, SolverError> {
    let baseline_false = positive_replay_false_count(arena, originals, projected)?;
    let mut trial = projected.clone();
    let Some((kind, stats)) =
        repair_projected_branch_best_candidate(arena, originals, branch, &mut trial)?
    else {
        return Ok(None);
    };
    if scalar_closure_rejects_branch_candidate(
        arena,
        originals,
        disjunction,
        branch,
        baseline_false,
        &trial,
    )? {
        return Ok(None);
    }
    *projected = trial;
    Ok(Some((kind, stats)))
}

fn project_replay_ext_candidate(
    arena: &TermArena,
    ctx: &RowCtx,
    originals: &[TermId],
    assignment: &Assignment,
) -> Result<ExtReplay, SolverError> {
    const MAX_TARGETED_REPLAY_REPAIRS: usize = 8;

    // Reconstruct array variables from the base-variable read sites only.
    let arrays = collect_base_array_entries(arena, ctx, assignment, "lazy-ext projection failed")?;
    let mut projected = complete_assignment(arena, assignment);
    for (&array, entries) in &arrays {
        projected.set(array, array_value_from_entries(arena, array, entries)?);
    }
    let mut repair_stats = repair_projected_ext_candidate(arena, originals, &mut projected)?;

    // Replay against the ORIGINAL assertions, re-deriving every array (dis)equality
    // extensionally from the reconstructed arrays. Accept only a genuine model;
    // a replay miss (reconstruction underdetermined this shape) declines.
    for _ in 0..MAX_TARGETED_REPLAY_REPAIRS {
        let Some(failure) =
            first_projected_replay_failure(arena, originals, &projected, repair_stats)?
        else {
            return Ok(ExtReplay::Sat(model_from_projected_assignment(
                arena, &projected,
            )));
        };
        let Some(targeted_stats) =
            repair_projected_replay_failure(arena, originals, &mut projected, &failure)?
        else {
            let failure = replay_failure_with_branch_candidate_diagnostics(
                arena, originals, &projected, failure,
            )?;
            return Ok(ExtReplay::Failed(Box::new(failure)));
        };
        repair_stats.absorb(targeted_stats);
    }

    if let Some(failure) =
        first_projected_replay_failure(arena, originals, &projected, repair_stats)?
    {
        let failure = replay_failure_with_branch_candidate_diagnostics(
            arena, originals, &projected, failure,
        )?;
        return Ok(ExtReplay::Failed(Box::new(failure)));
    }

    Ok(ExtReplay::Sat(model_from_projected_assignment(
        arena, &projected,
    )))
}

fn model_from_projected_assignment(arena: &TermArena, projected: &Assignment) -> Model {
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
    out
}

fn first_false_replay_conjunct(
    arena: &TermArena,
    assertion: TermId,
    assertion_ordinal: usize,
    assignment: &Assignment,
    repair_stats: ProjectionRepairStats,
) -> Result<ReplayFailure, SolverError> {
    let mut conjuncts = Vec::new();
    collect_positive_conjuncts(arena, assertion, &mut conjuncts);
    for (conjunct_ordinal, conjunct) in conjuncts.iter().copied().enumerate() {
        match eval(arena, conjunct, assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                let failed_eq = replay_failed_eq_details(arena, conjunct, assignment)?;
                let failed_or = replay_failed_or_details(arena, conjunct, assignment)?;
                return Ok(ReplayFailure {
                    assertion_ordinal,
                    assertion_term: assertion,
                    conjunct_ordinal,
                    conjunct_term: conjunct,
                    failed_eq,
                    failed_or,
                    select_candidate_diagnostics: Vec::new(),
                    branch_candidate_diagnostics: Vec::new(),
                    branch_select_candidate_diagnostics: Vec::new(),
                    branch_pair_candidate_diagnostics: Vec::new(),
                    repair_stats,
                });
            }
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "lazy-ext replay: conjunct #{} of assertion #{} evaluated to non-Boolean \
                     {value}",
                    conjunct.index(),
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "lazy-ext replay: conjunct #{} of assertion #{} failed evaluation: {error}",
                    conjunct.index(),
                    assertion.index()
                )));
            }
        }
    }
    Ok(ReplayFailure {
        assertion_ordinal,
        assertion_term: assertion,
        conjunct_ordinal: 0,
        conjunct_term: assertion,
        failed_eq: replay_failed_eq_details(arena, assertion, assignment)?,
        failed_or: replay_failed_or_details(arena, assertion, assignment)?,
        select_candidate_diagnostics: Vec::new(),
        branch_candidate_diagnostics: Vec::new(),
        branch_select_candidate_diagnostics: Vec::new(),
        branch_pair_candidate_diagnostics: Vec::new(),
        repair_stats,
    })
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
        ExtReplay, LastExtReplay, ProjectionRepairStats, RowCtx, RowKind, RowSite, StoreChainSide,
        array_value_from_entries, check_qf_abv_lazy, check_with_array_elimination,
        collect_base_array_entries, complete_assignment, const_array_default_mismatch_refutation,
        cross_store_array_disequality_refutation, default_value_for_symbol,
        first_false_replay_conjunct, first_projected_replay_failure, positive_replay_false_count,
        project_replay_ext_candidate, prove_unsat_by_symmetric_swap_chain,
        repair_projected_branch_as_candidate,
        repair_projected_branch_best_candidate_with_scalar_closure_guard,
        repair_projected_branch_scalar_choice_candidate, repair_projected_replay_branch_beam,
        repair_projected_replay_branch_choice, repair_projected_replay_branch_pair_choice,
        repair_projected_replay_branch_select_cycle, repair_projected_replay_failure,
        replay_failure_with_branch_candidate_diagnostics, replay_last_ext_candidate, select_value,
        store_chain_readback_refutation, store_value,
    };
    use crate::backend::{CheckResult, SolverConfig};
    use crate::sat_bv_backend::SatBvBackend;
    use axeyum_ir::{Assignment, Sort, TermArena, TermNode, Value, eval};
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
    fn lazy_ext_last_candidate_replay_accepts_only_real_models() {
        // The timeout/unknown shortcut is sound only because it rebuilds a model
        // and evaluates the original assertions. This pins the positive path:
        // even if refinement is incomplete, a candidate that replays is a real
        // SAT model.
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 16, 8).unwrap();
        let b = arena.array_var("b", 16, 8).unwrap();
        let c = arena.array_var("c", 16, 8).unwrap();
        let i = arena.bv_var("i", 16).unwrap();
        let j = arena.bv_var("j", 16).unwrap();
        let k = arena.bv_var("k", 16).unwrap();
        let v = arena.bv_var("v", 8).unwrap();
        let p = arena.bool_var("p").unwrap();
        let zero = arena.bv_const(8, 0).unwrap();

        let lhs = arena.store(a, i, v).unwrap();
        let rhs = arena.store(b, i, v).unwrap();
        let array_eq = arena.eq(lhs, rhs).unwrap();
        let cj = arena.select(c, j).unwrap();
        let ck = arena.select(c, k).unwrap();
        let cj_zero = arena.eq(cj, zero).unwrap();
        let ck_zero = arena.eq(ck, zero).unwrap();
        let loose_j = arena.or(cj_zero, p).unwrap();
        let loose_k = arena.or(ck_zero, p).unwrap();
        let originals = [array_eq, loose_j, loose_k, p];

        let mut ctx = RowCtx::default();
        for &assertion in &originals {
            ctx.abstract_with_array_eq(&mut arena, assertion)
                .unwrap()
                .expect("lazy-ext abstraction");
        }

        let mut candidate = Assignment::new();
        let mut row_value = 1u128;
        for (symbol, name, sort) in arena.symbols() {
            if name.starts_with("!ext_eq_") || name == "p" {
                candidate.set(symbol, Value::Bool(true));
            } else if name.starts_with("!row_sel_") {
                candidate.set(
                    symbol,
                    Value::Bv {
                        width: 8,
                        value: row_value,
                    },
                );
                row_value ^= 1;
            } else if sort == Sort::BitVec(16) {
                candidate.set(
                    symbol,
                    Value::Bv {
                        width: 16,
                        value: 0,
                    },
                );
            } else if sort == Sort::BitVec(8) {
                candidate.set(symbol, Value::Bv { width: 8, value: 0 });
            }
        }

        let LastExtReplay::Sat(model) =
            replay_last_ext_candidate(&arena, &ctx, &originals, Some(&candidate))
        else {
            panic!("expected replay helper to accept the candidate");
        };
        let assignment = model.to_assignment();
        for &t in &originals {
            assert_eq!(eval(&arena, t, &assignment).unwrap(), Value::Bool(true));
        }

        let mut failing = candidate.clone();
        for (symbol, name, _sort) in arena.symbols() {
            if name == "p" {
                failing.set(symbol, Value::Bool(false));
            }
        }
        let LastExtReplay::Failed(failure) =
            replay_last_ext_candidate(&arena, &ctx, &originals, Some(&failing))
        else {
            panic!("expected replay helper to reject the candidate");
        };
        assert_eq!(failure.assertion_ordinal, 3);
        assert_eq!(failure.assertion_term, p);
        assert_eq!(failure.conjunct_ordinal, 0);
        assert_eq!(failure.conjunct_term, p);
        assert!(failure.note().contains("failed_conjunct_term="));
    }

    #[test]
    fn lazy_ext_replay_failure_reports_best_false_or_branch() {
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let y = arena.int_var("y").unwrap();
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let two = arena.int_const(2);
        let x_eq_zero = arena.eq(x, zero).unwrap();
        let y_eq_zero = arena.eq(y, zero).unwrap();
        let x_eq_one = arena.eq(x, one).unwrap();
        let y_eq_two = arena.eq(y, two).unwrap();
        let branch0 = arena.and(x_eq_zero, y_eq_zero).unwrap();
        let branch1 = arena.and(x_eq_one, y_eq_two).unwrap();
        let assertion = arena.or(branch0, branch1).unwrap();

        let mut assignment = Assignment::new();
        let TermNode::Symbol(x_sym) = arena.node(x) else {
            panic!("x should be a symbol");
        };
        let TermNode::Symbol(y_sym) = arena.node(y) else {
            panic!("y should be a symbol");
        };
        assignment.set(*x_sym, Value::Int(1));
        assignment.set(*y_sym, Value::Int(3));

        let failure = first_false_replay_conjunct(
            &arena,
            assertion,
            0,
            &assignment,
            ProjectionRepairStats::default(),
        )
        .unwrap();
        let note = failure.note();
        assert!(note.contains("failed_or_branches=2"));
        assert!(note.contains("failed_or_best_branch=1"));
        assert!(note.contains("failed_or_best_branch_false_literals=1"));
        assert!(note.contains("failed_or_best_branch_first_false_term="));
        assert!(note.contains("failed_or_best_branch_first_false_lhs_value=3"));
    }

    #[test]
    fn lazy_ext_replay_failure_reports_branch_candidate_diagnostics() {
        let mut arena = TermArena::new();
        let q = arena.bool_var("q").unwrap();
        let r = arena.bool_var("r").unwrap();
        let branch_assertion = arena.or(q, r).unwrap();

        let TermNode::Symbol(q_symbol) = arena.node(q) else {
            panic!("q should be a symbol");
        };
        let TermNode::Symbol(r_symbol) = arena.node(r) else {
            panic!("r should be a symbol");
        };

        let mut candidate = Assignment::new();
        candidate.set(*q_symbol, Value::Bool(false));
        candidate.set(*r_symbol, Value::Bool(false));

        let ctx = RowCtx::default();
        let originals = [branch_assertion];
        let ExtReplay::Failed(failure) =
            project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
        else {
            panic!("expected unrepairable branch replay failure");
        };
        let note = failure.note();
        assert!(note.contains("branch_candidate_diagnostics=["));
        assert!(note.contains("#0:init=1,status=no_repair"));
        assert!(note.contains("#1:init=1,status=no_repair"));
    }

    #[test]
    fn lazy_ext_branch_pair_choice_scores_adjacent_or_repairs() {
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let y = arena.int_var("y").unwrap();
        let q = arena.bool_var("q").unwrap();
        let one = arena.int_const(1);
        let two = arena.int_const(2);
        let x_eq_one = arena.eq(x, one).unwrap();
        let y_eq_one = arena.eq(y, one).unwrap();
        let first_or = arena.or(x_eq_one, y_eq_one).unwrap();
        let x_eq_two = arena.eq(x, two).unwrap();
        let second_or = arena.or(x_eq_two, q).unwrap();

        let TermNode::Symbol(x_symbol) = arena.node(x) else {
            panic!("x should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };
        let TermNode::Symbol(q_symbol) = arena.node(q) else {
            panic!("q should be a symbol");
        };

        let mut projected = Assignment::new();
        projected.set(*x_symbol, Value::Int(0));
        projected.set(*y_symbol, Value::Int(0));
        projected.set(*q_symbol, Value::Bool(false));
        let originals = [first_or, second_or];
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            2
        );

        let mut single = projected.clone();
        repair_projected_replay_branch_choice(&arena, &originals, first_or, &mut single)
            .unwrap()
            .expect("single-OR repair should choose the local branch tie");
        assert_eq!(single.get(*x_symbol), Some(Value::Int(1)));
        assert_eq!(single.get(*y_symbol), Some(Value::Int(0)));
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &single).unwrap(),
            1
        );

        let mut paired = projected;
        repair_projected_replay_branch_pair_choice(&arena, &originals, first_or, &mut paired)
            .unwrap()
            .expect("paired repair should compose adjacent OR choices");
        assert_eq!(paired.get(*x_symbol), Some(Value::Int(2)));
        assert_eq!(paired.get(*y_symbol), Some(Value::Int(1)));
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &paired).unwrap(),
            0
        );
        for &original in &originals {
            assert_eq!(eval(&arena, original, &paired).unwrap(), Value::Bool(true));
        }
    }

    #[test]
    fn lazy_ext_branch_beam_allows_temporary_uphill_schedule() {
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let y = arena.int_var("y").unwrap();
        let z = arena.int_var("z").unwrap();
        let w = arena.int_var("w").unwrap();
        let q = arena.bool_var("q").unwrap();
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let two = arena.int_const(2);
        let three = arena.int_const(3);

        let x_eq_one = arena.eq(x, one).unwrap();
        let first_or = arena.or(x_eq_one, q).unwrap();
        let x_eq_zero = arena.eq(x, zero).unwrap();
        let z_eq_one = arena.eq(z, one).unwrap();
        let second_or = arena.or(x_eq_zero, z_eq_one).unwrap();
        let z_eq_zero = arena.eq(z, zero).unwrap();
        let y_eq_two = arena.eq(y, two).unwrap();
        let third_or = arena.or(z_eq_zero, y_eq_two).unwrap();
        let w_eq_three = arena.eq(w, three).unwrap();
        let fourth_or = arena.or(z_eq_zero, w_eq_three).unwrap();
        let prefix = arena.and(first_or, second_or).unwrap();
        let suffix = arena.and(third_or, fourth_or).unwrap();
        let assertion = arena.and(prefix, suffix).unwrap();

        let TermNode::Symbol(x_symbol) = arena.node(x) else {
            panic!("x should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };
        let TermNode::Symbol(z_symbol) = arena.node(z) else {
            panic!("z should be a symbol");
        };
        let TermNode::Symbol(w_symbol) = arena.node(w) else {
            panic!("w should be a symbol");
        };
        let TermNode::Symbol(q_symbol) = arena.node(q) else {
            panic!("q should be a symbol");
        };

        let mut projected = Assignment::new();
        projected.set(*x_symbol, Value::Int(0));
        projected.set(*y_symbol, Value::Int(0));
        projected.set(*z_symbol, Value::Int(0));
        projected.set(*w_symbol, Value::Int(0));
        projected.set(*q_symbol, Value::Bool(false));
        let originals = [assertion];
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            1
        );

        let mut paired = projected.clone();
        assert!(
            repair_projected_replay_branch_pair_choice(&arena, &originals, first_or, &mut paired)
                .unwrap()
                .is_none(),
            "strict pair repair should reject the temporary two-false state"
        );

        let stats =
            repair_projected_replay_branch_beam(&arena, &originals, first_or, &mut projected)
                .unwrap()
                .expect("beam should find the final improving branch schedule");
        assert!(stats.branch_symbol_changes >= 4);
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            0
        );
        assert_eq!(projected.get(*x_symbol), Some(Value::Int(1)));
        assert_eq!(projected.get(*z_symbol), Some(Value::Int(1)));
        assert_eq!(projected.get(*y_symbol), Some(Value::Int(2)));
        assert_eq!(projected.get(*w_symbol), Some(Value::Int(3)));
        assert_eq!(
            eval(&arena, assertion, &projected).unwrap(),
            Value::Bool(true)
        );
    }

    #[test]
    fn lazy_ext_branch_beam_stabilizes_direct_select_readbacks() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let b = arena.array_var("b", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let v = arena.bv_var("v", 8).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let p = arena.bool_var("p").unwrap();
        let stored = arena.store(b, i, v).unwrap();
        let a_eq_store = arena.eq(a, stored).unwrap();
        let branch_or = arena.or(a_eq_store, p).unwrap();
        let read_a_i = arena.select(a, i).unwrap();
        let y_eq_read = arena.eq(y, read_a_i).unwrap();
        let assertion = arena.and(branch_or, y_eq_read).unwrap();

        let TermNode::Symbol(a_symbol) = arena.node(a) else {
            panic!("a should be a symbol");
        };
        let TermNode::Symbol(b_symbol) = arena.node(b) else {
            panic!("b should be a symbol");
        };
        let TermNode::Symbol(i_symbol) = arena.node(i) else {
            panic!("i should be a symbol");
        };
        let TermNode::Symbol(v_symbol) = arena.node(v) else {
            panic!("v should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };
        let TermNode::Symbol(p_symbol) = arena.node(p) else {
            panic!("p should be a symbol");
        };

        let mut projected = Assignment::new();
        let default_a = default_value_for_symbol(&arena, *a_symbol).unwrap();
        let default_b = default_value_for_symbol(&arena, *b_symbol).unwrap();
        projected.set(*a_symbol, default_a);
        projected.set(*b_symbol, default_b);
        projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });
        projected.set(*v_symbol, Value::Bv { width: 8, value: 7 });
        projected.set(*y_symbol, Value::Bv { width: 8, value: 0 });
        projected.set(*p_symbol, Value::Bool(false));

        let originals = [assertion];
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            1
        );
        repair_projected_replay_branch_beam(&arena, &originals, branch_or, &mut projected)
            .unwrap()
            .expect("beam should repair the store branch and align readback");
        assert_eq!(
            projected.get(*y_symbol),
            Some(Value::Bv { width: 8, value: 7 })
        );
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            0
        );
        assert_eq!(
            eval(&arena, assertion, &projected).unwrap(),
            Value::Bool(true)
        );
    }

    #[test]
    fn lazy_ext_replay_failure_reports_branch_pair_candidate_diagnostics() {
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let y = arena.int_var("y").unwrap();
        let q = arena.bool_var("q").unwrap();
        let h = arena.bool_var("h").unwrap();
        let one = arena.int_const(1);
        let two = arena.int_const(2);
        let x_eq_one = arena.eq(x, one).unwrap();
        let y_eq_one = arena.eq(y, one).unwrap();
        let first_or = arena.or(x_eq_one, y_eq_one).unwrap();
        let x_eq_two = arena.eq(x, two).unwrap();
        let second_or = arena.or(x_eq_two, q).unwrap();
        let first_two = arena.and(first_or, second_or).unwrap();
        let assertion = arena.and(first_two, h).unwrap();

        let TermNode::Symbol(x_symbol) = arena.node(x) else {
            panic!("x should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };
        let TermNode::Symbol(q_symbol) = arena.node(q) else {
            panic!("q should be a symbol");
        };
        let TermNode::Symbol(h_symbol) = arena.node(h) else {
            panic!("h should be a symbol");
        };

        let mut projected = Assignment::new();
        projected.set(*x_symbol, Value::Int(0));
        projected.set(*y_symbol, Value::Int(0));
        projected.set(*q_symbol, Value::Bool(false));
        projected.set(*h_symbol, Value::Bool(false));
        let originals = [assertion];
        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected first OR replay failure");
        let failure = replay_failure_with_branch_candidate_diagnostics(
            &arena, &originals, &projected, failure,
        )
        .unwrap();
        let note = failure.note();
        assert!(note.contains("branch_pair_candidate_diagnostics=["));
        assert!(note.contains("#1->1#0:init=1,status=candidate"), "{note}");
        assert!(note.contains("global_false_ordinal=2"), "{note}");
    }

    #[test]
    fn lazy_ext_replay_failure_reports_branch_select_candidate_diagnostics() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let j = arena.bv_var("j", 4).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let q = arena.bool_var("q").unwrap();
        let i_eq_j = arena.eq(i, j).unwrap();
        let branch_or = arena.or(i_eq_j, q).unwrap();
        let read = arena.select(a, i).unwrap();
        let y_eq_read = arena.eq(y, read).unwrap();
        let assertion = arena.and(branch_or, y_eq_read).unwrap();

        let TermNode::Symbol(a_symbol) = arena.node(a) else {
            panic!("a should be a symbol");
        };
        let TermNode::Symbol(i_symbol) = arena.node(i) else {
            panic!("i should be a symbol");
        };
        let TermNode::Symbol(j_symbol) = arena.node(j) else {
            panic!("j should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };
        let TermNode::Symbol(q_symbol) = arena.node(q) else {
            panic!("q should be a symbol");
        };

        let mut projected = Assignment::new();
        let default_a = default_value_for_symbol(&arena, *a_symbol).unwrap();
        let a_with_entry = store_value(
            &default_a,
            Value::Bv { width: 4, value: 2 },
            Value::Bv { width: 8, value: 7 },
        )
        .unwrap();
        projected.set(*a_symbol, a_with_entry);
        projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });
        projected.set(*j_symbol, Value::Bv { width: 4, value: 2 });
        projected.set(*y_symbol, Value::Bv { width: 8, value: 0 });
        projected.set(*q_symbol, Value::Bool(false));

        let originals = [assertion];
        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected first OR replay failure");
        let failure = replay_failure_with_branch_candidate_diagnostics(
            &arena, &originals, &projected, failure,
        )
        .unwrap();
        let note = failure.note();
        assert!(note.contains("branch_select_candidate_diagnostics=["));
        assert!(note.contains("#0->1:direct,status=candidate"), "{note}");
        assert!(note.contains("target_true=true"), "{note}");
        assert!(note.contains("total_false=0"), "{note}");
    }

    #[test]
    fn lazy_ext_branch_select_cycle_repair_forces_alternate_or_branch() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let b = arena.array_var("b", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let q = arena.bool_var("q").unwrap();
        let two4 = arena.bv_const(4, 2).unwrap();
        let three4 = arena.bv_const(4, 3).unwrap();
        let zero8 = arena.bv_const(8, 0).unwrap();
        let seven8 = arena.bv_const(8, 7).unwrap();
        let nine8 = arena.bv_const(8, 9).unwrap();
        let true_term = arena.bool_const(true);
        let i_eq_two = arena.eq(i, two4).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let copy_branch = arena.and(i_eq_two, a_eq_b).unwrap();
        let q_eq_true = arena.eq(q, true_term).unwrap();
        let branch_or = arena.or(copy_branch, q_eq_true).unwrap();
        let read_a_i = arena.select(a, i).unwrap();
        let zero_eq_read = arena.eq(zero8, read_a_i).unwrap();
        let read_b_two = arena.select(b, two4).unwrap();
        let seven_eq_read = arena.eq(seven8, read_b_two).unwrap();
        let read_b_three = arena.select(b, three4).unwrap();
        let nine_eq_read = arena.eq(nine8, read_b_three).unwrap();
        let first = arena.and(branch_or, zero_eq_read).unwrap();
        let second = arena.and(seven_eq_read, nine_eq_read).unwrap();
        let assertion = arena.and(first, second).unwrap();

        let TermNode::Symbol(a_symbol) = arena.node(a) else {
            panic!("a should be a symbol");
        };
        let TermNode::Symbol(b_symbol) = arena.node(b) else {
            panic!("b should be a symbol");
        };
        let TermNode::Symbol(i_symbol) = arena.node(i) else {
            panic!("i should be a symbol");
        };
        let TermNode::Symbol(q_symbol) = arena.node(q) else {
            panic!("q should be a symbol");
        };

        let mut projected = Assignment::new();
        projected.set(
            *a_symbol,
            default_value_for_symbol(&arena, *a_symbol).unwrap(),
        );
        let default_b = default_value_for_symbol(&arena, *b_symbol).unwrap();
        let b_with_two = store_value(
            &default_b,
            Value::Bv { width: 4, value: 2 },
            Value::Bv { width: 8, value: 7 },
        )
        .unwrap();
        let b_with_entries = store_value(
            &b_with_two,
            Value::Bv { width: 4, value: 3 },
            Value::Bv { width: 8, value: 9 },
        )
        .unwrap();
        projected.set(*b_symbol, b_with_entries);
        projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });
        projected.set(*q_symbol, Value::Bool(false));

        let originals = [assertion];
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            1
        );
        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected first OR replay failure");
        let failure = replay_failure_with_branch_candidate_diagnostics(
            &arena, &originals, &projected, failure,
        )
        .unwrap();
        let note = failure.note();
        assert!(
            note.contains("branch_select_candidate_diagnostics=["),
            "{note}"
        );
        assert!(
            note.contains("global_false_or_best_branch=0")
                || note.contains("global_false_or_best_branch=1"),
            "{note}"
        );
        assert!(
            note.contains("global_false_or_best_branch_false_literals=1"),
            "{note}"
        );
        let stats = repair_projected_replay_branch_select_cycle(
            &arena,
            &originals,
            branch_or,
            &mut projected,
        )
        .unwrap()
        .expect("expected branch/select cycle repair");
        assert!(stats.branch_symbol_changes >= 2, "{stats:?}");
        assert!(stats.array_changes >= 1, "{stats:?}");
        assert_eq!(projected.get(*q_symbol), Some(Value::Bool(true)));
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            0
        );
    }

    #[test]
    fn lazy_ext_branch_select_cycle_repairs_same_branch_store_residual() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let c = arena.array_var("c", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let two4 = arena.bv_const(4, 2).unwrap();
        let three4 = arena.bv_const(4, 3).unwrap();
        let five8 = arena.bv_const(8, 5).unwrap();
        let seven8 = arena.bv_const(8, 7).unwrap();
        let false_term = arena.bool_const(false);
        let i_eq_two = arena.eq(i, two4).unwrap();
        let store_a_three = arena.store(a, three4, seven8).unwrap();
        let c_eq_store = arena.eq(c, store_a_three).unwrap();
        let store_branch = arena.and(i_eq_two, c_eq_store).unwrap();
        let blocked_branch = arena.and(false_term, false_term).unwrap();
        let branch_or = arena.or(store_branch, blocked_branch).unwrap();
        let read_a_i = arena.select(a, i).unwrap();
        let five_eq_read = arena.eq(five8, read_a_i).unwrap();
        let assertion = arena.and(branch_or, five_eq_read).unwrap();

        let TermNode::Symbol(a_symbol) = arena.node(a) else {
            panic!("a should be a symbol");
        };
        let TermNode::Symbol(c_symbol) = arena.node(c) else {
            panic!("c should be a symbol");
        };
        let TermNode::Symbol(i_symbol) = arena.node(i) else {
            panic!("i should be a symbol");
        };

        let mut projected = Assignment::new();
        projected.set(
            *a_symbol,
            default_value_for_symbol(&arena, *a_symbol).unwrap(),
        );
        projected.set(
            *c_symbol,
            default_value_for_symbol(&arena, *c_symbol).unwrap(),
        );
        projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });

        let originals = [assertion];
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            2
        );
        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected first OR replay failure");
        let failure = replay_failure_with_branch_candidate_diagnostics(
            &arena, &originals, &projected, failure,
        )
        .unwrap();
        let note = failure.note();
        assert!(
            note.contains("chain+same_branch_store_target,status=candidate"),
            "{note}"
        );
        assert!(note.contains("total_false=0"), "{note}");

        let stats = repair_projected_replay_branch_select_cycle(
            &arena,
            &originals,
            branch_or,
            &mut projected,
        )
        .unwrap()
        .expect("expected same-branch store residual repair");
        assert!(stats.branch_symbol_changes >= 2, "{stats:?}");
        assert!(stats.array_changes >= 1, "{stats:?}");
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            0
        );
        assert_eq!(
            eval(&arena, five_eq_read, &projected).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&arena, c_eq_store, &projected).unwrap(),
            Value::Bool(true)
        );
    }

    #[test]
    fn lazy_ext_replay_failure_reports_residual_followup_or_diagnostic() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let c = arena.array_var("c", 4, 8).unwrap();
        let d = arena.array_var("d", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let two4 = arena.bv_const(4, 2).unwrap();
        let three4 = arena.bv_const(4, 3).unwrap();
        let five8 = arena.bv_const(8, 5).unwrap();
        let seven8 = arena.bv_const(8, 7).unwrap();
        let false_term = arena.bool_const(false);
        let i_eq_two = arena.eq(i, two4).unwrap();
        let store_a_three = arena.store(a, three4, seven8).unwrap();
        let c_eq_store = arena.eq(c, store_a_three).unwrap();
        let store_branch = arena.and(i_eq_two, c_eq_store).unwrap();
        let blocked_branch = arena.and(false_term, false_term).unwrap();
        let first_or = arena.or(store_branch, blocked_branch).unwrap();
        let read_a_i = arena.select(a, i).unwrap();
        let five_eq_read = arena.eq(five8, read_a_i).unwrap();
        let d_eq_c = arena.eq(d, c).unwrap();
        let second_or = arena.or(d_eq_c, blocked_branch).unwrap();
        let first = arena.and(first_or, five_eq_read).unwrap();
        let assertion = arena.and(first, second_or).unwrap();

        let TermNode::Symbol(a_symbol) = arena.node(a) else {
            panic!("a should be a symbol");
        };
        let TermNode::Symbol(c_symbol) = arena.node(c) else {
            panic!("c should be a symbol");
        };
        let TermNode::Symbol(d_symbol) = arena.node(d) else {
            panic!("d should be a symbol");
        };
        let TermNode::Symbol(i_symbol) = arena.node(i) else {
            panic!("i should be a symbol");
        };

        let mut projected = Assignment::new();
        projected.set(
            *a_symbol,
            default_value_for_symbol(&arena, *a_symbol).unwrap(),
        );
        projected.set(
            *c_symbol,
            default_value_for_symbol(&arena, *c_symbol).unwrap(),
        );
        let default_d = default_value_for_symbol(&arena, *d_symbol).unwrap();
        let d_with_entry = store_value(
            &default_d,
            Value::Bv { width: 4, value: 1 },
            Value::Bv { width: 8, value: 9 },
        )
        .unwrap();
        projected.set(*d_symbol, d_with_entry);
        projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });

        let originals = [assertion];
        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected first OR replay failure");
        let failure = replay_failure_with_branch_candidate_diagnostics(
            &arena, &originals, &projected, failure,
        )
        .unwrap();
        let note = failure.note();
        assert!(
            note.contains("chain+same_branch_store_target,status=candidate"),
            "{note}"
        );
        assert!(
            note.contains("chain+same_branch_store_target+followup_or"),
            "{note}"
        );
        assert!(note.contains("target_true=true"), "{note}");
        assert!(note.contains("total_false=0"), "{note}");
    }

    #[test]
    fn lazy_ext_branch_select_cycle_repairs_residual_followup_or_chain() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let c = arena.array_var("c", 4, 8).unwrap();
        let d = arena.array_var("d", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let two4 = arena.bv_const(4, 2).unwrap();
        let three4 = arena.bv_const(4, 3).unwrap();
        let five8 = arena.bv_const(8, 5).unwrap();
        let seven8 = arena.bv_const(8, 7).unwrap();
        let false_term = arena.bool_const(false);
        let i_eq_two = arena.eq(i, two4).unwrap();
        let store_a_three = arena.store(a, three4, seven8).unwrap();
        let c_eq_store = arena.eq(c, store_a_three).unwrap();
        let store_branch = arena.and(i_eq_two, c_eq_store).unwrap();
        let blocked_branch = arena.and(false_term, false_term).unwrap();
        let first_or = arena.or(store_branch, blocked_branch).unwrap();
        let read_a_i = arena.select(a, i).unwrap();
        let five_eq_read = arena.eq(five8, read_a_i).unwrap();
        let d_eq_c = arena.eq(d, c).unwrap();
        let second_or = arena.or(d_eq_c, blocked_branch).unwrap();
        let first = arena.and(first_or, five_eq_read).unwrap();
        let assertion = arena.and(first, second_or).unwrap();

        let TermNode::Symbol(a_symbol) = arena.node(a) else {
            panic!("a should be a symbol");
        };
        let TermNode::Symbol(c_symbol) = arena.node(c) else {
            panic!("c should be a symbol");
        };
        let TermNode::Symbol(d_symbol) = arena.node(d) else {
            panic!("d should be a symbol");
        };
        let TermNode::Symbol(i_symbol) = arena.node(i) else {
            panic!("i should be a symbol");
        };

        let default_a = default_value_for_symbol(&arena, *a_symbol).unwrap();
        let default_c = default_value_for_symbol(&arena, *c_symbol).unwrap();
        let default_d = default_value_for_symbol(&arena, *d_symbol).unwrap();
        let mut projected = Assignment::new();
        projected.set(*a_symbol, default_a);
        projected.set(*c_symbol, default_c);
        projected.set(*d_symbol, default_d);
        projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });

        let originals = [assertion];
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            2
        );
        let stats = repair_projected_replay_branch_select_cycle(
            &arena,
            &originals,
            first_or,
            &mut projected,
        )
        .unwrap()
        .expect("expected residual follow-up OR repair");
        assert!(stats.branch_symbol_changes >= 3, "{stats:?}");
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            0
        );
        assert_eq!(
            eval(&arena, five_eq_read, &projected).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&arena, c_eq_store, &projected).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(eval(&arena, d_eq_c, &projected).unwrap(), Value::Bool(true));
    }

    #[test]
    fn lazy_ext_scalar_branch_choice_prefers_replay_safe_direction() {
        let mut arena = TermArena::new();
        let u = arena.int_var("u").unwrap();
        let v = arena.int_var("v").unwrap();
        let zero = arena.int_const(0);
        let false_term = arena.bool_const(false);
        let u_eq_v = arena.eq(u, v).unwrap();
        let branch_or = arena.or(u_eq_v, false_term).unwrap();
        let u_eq_zero = arena.eq(u, zero).unwrap();
        let assertion = arena.and(branch_or, u_eq_zero).unwrap();

        let TermNode::Symbol(u_symbol) = arena.node(u) else {
            panic!("u should be a symbol");
        };
        let TermNode::Symbol(v_symbol) = arena.node(v) else {
            panic!("v should be a symbol");
        };

        let mut greedy = Assignment::new();
        greedy.set(*u_symbol, Value::Int(0));
        greedy.set(*v_symbol, Value::Int(1));
        let originals = [assertion];
        let greedy_stats =
            repair_projected_branch_as_candidate(&arena, &originals, u_eq_v, &mut greedy)
                .unwrap()
                .expect("expected greedy branch repair");
        assert!(greedy_stats.branch_symbol_changes >= 1);
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &greedy).unwrap(),
            1
        );

        let mut projected = Assignment::new();
        projected.set(*u_symbol, Value::Int(0));
        projected.set(*v_symbol, Value::Int(1));
        let stats = repair_projected_branch_scalar_choice_candidate(
            &arena,
            &originals,
            u_eq_v,
            &mut projected,
        )
        .unwrap()
        .expect("expected scalar choice repair");
        assert_eq!(stats.branch_symbol_changes, 1);
        assert_eq!(projected.get(*u_symbol), Some(Value::Int(0)));
        assert_eq!(projected.get(*v_symbol), Some(Value::Int(0)));
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            0
        );
    }

    #[test]
    fn lazy_ext_scalar_closure_guard_rejects_returned_or_loop() {
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let y = arena.int_var("y").unwrap();
        let z = arena.int_var("z").unwrap();
        let one = arena.int_const(1);
        let two = arena.int_const(2);
        let false_term = arena.bool_const(false);
        let y_eq_x = arena.eq(y, x).unwrap();
        let z_eq_x = arena.eq(z, x).unwrap();
        let branch = arena.and(y_eq_x, z_eq_x).unwrap();
        let disjunction = arena.or(branch, false_term).unwrap();
        let y_eq_one = arena.eq(y, one).unwrap();
        let z_eq_two = arena.eq(z, two).unwrap();
        let rest = arena.and(y_eq_one, z_eq_two).unwrap();
        let assertion = arena.and(disjunction, rest).unwrap();

        let TermNode::Symbol(x_symbol) = arena.node(x) else {
            panic!("x should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };
        let TermNode::Symbol(z_symbol) = arena.node(z) else {
            panic!("z should be a symbol");
        };

        let mut projected = Assignment::new();
        projected.set(*x_symbol, Value::Int(0));
        projected.set(*y_symbol, Value::Int(1));
        projected.set(*z_symbol, Value::Int(2));
        let originals = [assertion];
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            1
        );

        let mut raw_candidate = projected.clone();
        repair_projected_branch_as_candidate(&arena, &originals, branch, &mut raw_candidate)
            .unwrap()
            .expect("expected raw branch repair");
        assert_eq!(
            eval(&arena, disjunction, &raw_candidate).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &raw_candidate).unwrap(),
            2
        );

        let guarded = repair_projected_branch_best_candidate_with_scalar_closure_guard(
            &arena,
            &originals,
            disjunction,
            branch,
            &mut projected,
        )
        .unwrap();
        assert!(
            guarded.is_none(),
            "closure returns to the same OR without replay improvement"
        );
        assert_eq!(projected.get(*x_symbol), Some(Value::Int(0)));
        assert_eq!(projected.get(*y_symbol), Some(Value::Int(1)));
        assert_eq!(projected.get(*z_symbol), Some(Value::Int(2)));
    }

    #[test]
    fn lazy_ext_replay_failure_reports_scalar_choice_side_effects() {
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let y = arena.int_var("y").unwrap();
        let z = arena.int_var("z").unwrap();
        let zero = arena.int_const(0);
        let false_term = arena.bool_const(false);
        let x_eq_y = arena.eq(x, y).unwrap();
        let y_eq_z = arena.eq(y, z).unwrap();
        let branch = arena.and(x_eq_y, y_eq_z).unwrap();
        let blocked_branch = arena.and(false_term, false_term).unwrap();
        let branch_or = arena.or(branch, blocked_branch).unwrap();
        let x_eq_zero = arena.eq(x, zero).unwrap();
        let assertion = arena.and(branch_or, x_eq_zero).unwrap();

        let TermNode::Symbol(x_symbol) = arena.node(x) else {
            panic!("x should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };
        let TermNode::Symbol(z_symbol) = arena.node(z) else {
            panic!("z should be a symbol");
        };

        let mut projected = Assignment::new();
        projected.set(*x_symbol, Value::Int(0));
        projected.set(*y_symbol, Value::Int(1));
        projected.set(*z_symbol, Value::Int(2));

        let originals = [assertion];
        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected scalar OR replay failure");
        let failure = replay_failure_with_branch_candidate_diagnostics(
            &arena, &originals, &projected, failure,
        )
        .unwrap();
        let note = failure.note();
        assert!(
            note.contains("failed_or_best_branch_false_literal_details=["),
            "{note}"
        );
        assert!(note.contains(&format!("term={}", x_eq_y.index())), "{note}");
        assert!(note.contains(&format!("term={}", y_eq_z.index())), "{note}");
        assert!(note.contains("scalar_choices=("), "{note}");
        assert!(note.contains("literal_true=true"), "{note}");
        assert!(note.contains("branch_false=1"), "{note}");
        assert!(note.contains("global_false_term="), "{note}");
        assert!(
            note.contains("failed_or_best_branch_paired_scalar_chain=("),
            "{note}"
        );
        assert!(note.contains("branch_steps=["), "{note}");
        assert!(note.contains("followup_steps=[]"), "{note}");
        assert!(note.contains("final_branch_false=0"), "{note}");
        assert!(note.contains("final_total_false=0"), "{note}");
        assert!(
            note.contains("failed_or_scalar_closure_branch_candidates=["),
            "{note}"
        );
        assert!(note.contains("#0:init=2"), "{note}");
        assert!(note.contains("raw_branch_false=0"), "{note}");
        assert!(note.contains("final_branch_false=0"), "{note}");
        assert!(note.contains("final_total_false=0"), "{note}");
    }

    #[test]
    fn lazy_ext_replay_failure_reports_select_candidate_diagnostics() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let h = arena.bool_var("h").unwrap();
        let read = arena.select(a, i).unwrap();
        let y_eq_read = arena.eq(y, read).unwrap();
        let assertion = arena.and(y_eq_read, h).unwrap();

        let TermNode::Symbol(a_symbol) = arena.node(a) else {
            panic!("a should be a symbol");
        };
        let TermNode::Symbol(i_symbol) = arena.node(i) else {
            panic!("i should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };
        let TermNode::Symbol(h_symbol) = arena.node(h) else {
            panic!("h should be a symbol");
        };

        let mut projected = Assignment::new();
        let default_a = default_value_for_symbol(&arena, *a_symbol).unwrap();
        projected.set(*a_symbol, default_a);
        projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });
        projected.set(*y_symbol, Value::Bv { width: 8, value: 7 });
        projected.set(*h_symbol, Value::Bool(false));

        let originals = [assertion];
        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected select replay failure");
        let failure = replay_failure_with_branch_candidate_diagnostics(
            &arena, &originals, &projected, failure,
        )
        .unwrap();
        let note = failure.note();
        assert!(note.contains("select_candidate_diagnostics=["));
        assert!(note.contains("chain:status=candidate"), "{note}");
        assert!(note.contains("direct:status=candidate"), "{note}");
        assert!(note.contains("global_false_ordinal=1"), "{note}");
    }

    #[test]
    fn lazy_ext_select_repair_beam_composes_followup_or_repair() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let z = arena.bv_var("z", 8).unwrap();
        let x = arena.int_var("x").unwrap();
        let q = arena.bool_var("q").unwrap();
        let read = arena.select(a, i).unwrap();
        let y_eq_read = arena.eq(y, read).unwrap();
        let one = arena.int_const(1);
        let x_eq_one = arena.eq(x, one).unwrap();
        let branch_or = arena.or(x_eq_one, q).unwrap();
        let z_eq_read = arena.eq(z, read).unwrap();
        let zero8 = arena.bv_const(8, 0).unwrap();
        let z_eq_zero = arena.eq(z, zero8).unwrap();
        let prefix = arena.and(y_eq_read, branch_or).unwrap();
        let suffix = arena.and(z_eq_read, z_eq_zero).unwrap();
        let assertion = arena.and(prefix, suffix).unwrap();

        let TermNode::Symbol(a_symbol) = arena.node(a) else {
            panic!("a should be a symbol");
        };
        let TermNode::Symbol(i_symbol) = arena.node(i) else {
            panic!("i should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };
        let TermNode::Symbol(z_symbol) = arena.node(z) else {
            panic!("z should be a symbol");
        };
        let TermNode::Symbol(x_symbol) = arena.node(x) else {
            panic!("x should be a symbol");
        };
        let TermNode::Symbol(q_symbol) = arena.node(q) else {
            panic!("q should be a symbol");
        };

        let mut projected = Assignment::new();
        projected.set(
            *a_symbol,
            default_value_for_symbol(&arena, *a_symbol).unwrap(),
        );
        projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });
        projected.set(*y_symbol, Value::Bv { width: 8, value: 7 });
        projected.set(*z_symbol, Value::Bv { width: 8, value: 0 });
        projected.set(*x_symbol, Value::Int(0));
        projected.set(*q_symbol, Value::Bool(false));

        let originals = [assertion];
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            2
        );
        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected direct select replay failure");
        assert_eq!(failure.conjunct_term, y_eq_read);

        let stats = repair_projected_replay_failure(&arena, &originals, &mut projected, &failure)
            .unwrap()
            .expect("expected composed select/OR repair");
        assert!(stats.array_changes >= 1, "{stats:?}");
        assert!(stats.branch_symbol_changes >= 1, "{stats:?}");
        assert_eq!(projected.get(*x_symbol), Some(Value::Int(1)));
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            1
        );
        assert_eq!(
            first_projected_replay_failure(
                &arena,
                &originals,
                &projected,
                ProjectionRepairStats::default(),
            )
            .unwrap()
            .expect("only the dependent z readback should remain false")
            .conjunct_term,
            z_eq_read
        );
    }

    #[test]
    fn lazy_ext_or_repair_beam_composes_followup_select_repair() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let j = arena.bv_var("j", 4).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let q = arena.bool_var("q").unwrap();
        let h = arena.bool_var("h").unwrap();
        let i_eq_j = arena.eq(i, j).unwrap();
        let branch_or = arena.or(i_eq_j, q).unwrap();
        let read = arena.select(a, i).unwrap();
        let y_eq_read = arena.eq(y, read).unwrap();
        let zero8 = arena.bv_const(8, 0).unwrap();
        let y_eq_zero = arena.eq(y, zero8).unwrap();
        let prefix = arena.and(branch_or, y_eq_read).unwrap();
        let suffix = arena.and(y_eq_zero, h).unwrap();
        let assertion = arena.and(prefix, suffix).unwrap();

        let TermNode::Symbol(a_symbol) = arena.node(a) else {
            panic!("a should be a symbol");
        };
        let TermNode::Symbol(i_symbol) = arena.node(i) else {
            panic!("i should be a symbol");
        };
        let TermNode::Symbol(j_symbol) = arena.node(j) else {
            panic!("j should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };
        let TermNode::Symbol(q_symbol) = arena.node(q) else {
            panic!("q should be a symbol");
        };
        let TermNode::Symbol(h_symbol) = arena.node(h) else {
            panic!("h should be a symbol");
        };

        let mut projected = Assignment::new();
        let default_a = default_value_for_symbol(&arena, *a_symbol).unwrap();
        let a_value = store_value(
            &default_a,
            Value::Bv { width: 4, value: 2 },
            Value::Bv { width: 8, value: 7 },
        )
        .unwrap();
        projected.set(*a_symbol, a_value);
        projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });
        projected.set(*j_symbol, Value::Bv { width: 4, value: 2 });
        projected.set(*y_symbol, Value::Bv { width: 8, value: 0 });
        projected.set(*q_symbol, Value::Bool(false));
        projected.set(*h_symbol, Value::Bool(false));

        let originals = [assertion];
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            2
        );
        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected generated OR replay failure");
        assert_eq!(failure.conjunct_term, branch_or);

        let stats = repair_projected_replay_failure(&arena, &originals, &mut projected, &failure)
            .unwrap()
            .expect("expected composed OR/select repair");
        assert!(stats.branch_symbol_changes >= 1, "{stats:?}");
        assert!(stats.array_changes >= 1, "{stats:?}");
        assert_eq!(
            projected.get(*i_symbol),
            Some(Value::Bv { width: 4, value: 2 })
        );
        assert_eq!(
            positive_replay_false_count(&arena, &originals, &projected).unwrap(),
            1
        );
        assert_eq!(
            first_projected_replay_failure(
                &arena,
                &originals,
                &projected,
                ProjectionRepairStats::default(),
            )
            .unwrap()
            .expect("only h should remain false")
            .conjunct_term,
            h
        );
    }

    #[test]
    fn lazy_ext_projection_repairs_single_false_branch_symbol_equality() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let b = arena.array_var("b", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let j = arena.bv_var("j", 4).unwrap();
        let v = arena.bv_var("v", 8).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let z = arena.bv_var("z", 8).unwrap();
        let p = arena.bool_var("p").unwrap();
        let stored = arena.store(a, i, v).unwrap();
        let b_eq_stored = arena.eq(b, stored).unwrap();
        let branch_assertion = arena.or(b_eq_stored, p).unwrap();
        let read_b_j = arena.select(b, j).unwrap();
        let y_eq_read = arena.eq(y, read_b_j).unwrap();
        let read_a_j = arena.select(a, j).unwrap();
        let z_eq_base_read = arena.eq(z, read_a_j).unwrap();

        let mut candidate = Assignment::new();
        for (symbol, name, sort) in arena.symbols() {
            match name {
                "i" => candidate.set(symbol, Value::Bv { width: 4, value: 0 }),
                "j" => candidate.set(symbol, Value::Bv { width: 4, value: 1 }),
                "v" => candidate.set(symbol, Value::Bv { width: 8, value: 7 }),
                "y" => candidate.set(symbol, Value::Bv { width: 8, value: 3 }),
                "z" => candidate.set(symbol, Value::Bv { width: 8, value: 0 }),
                "p" => candidate.set(symbol, Value::Bool(false)),
                _ if sort == Sort::BitVec(4) => {
                    candidate.set(symbol, Value::Bv { width: 4, value: 0 });
                }
                _ if sort == Sort::BitVec(8) => {
                    candidate.set(symbol, Value::Bv { width: 8, value: 0 });
                }
                _ => {}
            }
        }

        let ctx = RowCtx::default();
        let originals = [branch_assertion, y_eq_read, z_eq_base_read];
        let ExtReplay::Sat(model) =
            project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
        else {
            panic!("expected branch-repaired projection to replay");
        };
        let assignment = model.to_assignment();
        let TermNode::Symbol(z_symbol) = arena.node(z) else {
            panic!("z should be a symbol");
        };
        assert_eq!(
            assignment.get(*z_symbol),
            Some(Value::Bv { width: 8, value: 3 })
        );
        for &original in &originals {
            assert_eq!(
                eval(&arena, original, &assignment).unwrap(),
                Value::Bool(true)
            );
        }
    }

    #[test]
    fn lazy_ext_targeted_replay_repairs_single_store_branch_literal() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let b = arena.array_var("b", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let v = arena.bv_var("v", 8).unwrap();
        let p = arena.bool_var("p").unwrap();
        let stored = arena.store(a, i, v).unwrap();
        let b_eq_store = arena.eq(b, stored).unwrap();
        let branch_assertion = arena.or(b_eq_store, p).unwrap();

        let mut candidate = Assignment::new();
        for (symbol, name, sort) in arena.symbols() {
            match name {
                "i" => candidate.set(symbol, Value::Bv { width: 4, value: 0 }),
                "v" => candidate.set(symbol, Value::Bv { width: 8, value: 7 }),
                "p" => candidate.set(symbol, Value::Bool(false)),
                _ if sort == Sort::BitVec(4) => {
                    candidate.set(symbol, Value::Bv { width: 4, value: 0 });
                }
                _ if sort == Sort::BitVec(8) => {
                    candidate.set(symbol, Value::Bv { width: 8, value: 0 });
                }
                _ => {}
            }
        }

        let originals = [branch_assertion];
        let mut projected = complete_assignment(&arena, &candidate);
        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected the store branch to fail before targeted repair");
        assert_eq!(failure.conjunct_term, branch_assertion);

        let stats = repair_projected_replay_failure(&arena, &originals, &mut projected, &failure)
            .unwrap()
            .expect("expected targeted branch repair to change the projection");
        assert_eq!(stats.branch_symbol_changes, 1);
        assert!(
            first_projected_replay_failure(
                &arena,
                &originals,
                &projected,
                ProjectionRepairStats::default(),
            )
            .unwrap()
            .is_none()
        );
    }

    #[test]
    fn lazy_ext_targeted_replay_repairs_direct_select_equality() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let read = arena.select(a, i).unwrap();
        let y_eq_read = arena.eq(y, read).unwrap();

        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };

        let mut candidate = Assignment::new();
        for (symbol, name, sort) in arena.symbols() {
            match name {
                "i" => candidate.set(symbol, Value::Bv { width: 4, value: 1 }),
                "y" => candidate.set(symbol, Value::Bv { width: 8, value: 7 }),
                _ if sort == Sort::BitVec(4) => {
                    candidate.set(symbol, Value::Bv { width: 4, value: 0 });
                }
                _ if sort == Sort::BitVec(8) => {
                    candidate.set(symbol, Value::Bv { width: 8, value: 0 });
                }
                _ => {}
            }
        }

        let originals = [y_eq_read];
        let mut projected = complete_assignment(&arena, &candidate);
        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected the direct select equality to fail before repair");

        let stats = repair_projected_replay_failure(&arena, &originals, &mut projected, &failure)
            .unwrap()
            .expect("expected targeted select repair to change the projection");
        assert_eq!(stats.array_changes, 1);
        assert_eq!(
            projected.get(*y_symbol),
            Some(Value::Bv { width: 8, value: 7 })
        );
        assert!(
            first_projected_replay_failure(
                &arena,
                &originals,
                &projected,
                ProjectionRepairStats::default(),
            )
            .unwrap()
            .is_none()
        );
    }

    #[test]
    fn lazy_ext_targeted_replay_repairs_select_through_store_chain() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let b = arena.array_var("b", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let j = arena.bv_var("j", 4).unwrap();
        let v = arena.bv_var("v", 8).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let p = arena.bool_var("p").unwrap();
        let stored = arena.store(a, j, v).unwrap();
        let b_eq_store = arena.eq(b, stored).unwrap();
        let branch_assertion = arena.or(b_eq_store, p).unwrap();
        let read_b_i = arena.select(b, i).unwrap();
        let y_eq_read = arena.eq(y, read_b_i).unwrap();

        let TermNode::Symbol(a_symbol) = arena.node(a) else {
            panic!("a should be a symbol");
        };
        let TermNode::Symbol(b_symbol) = arena.node(b) else {
            panic!("b should be a symbol");
        };

        let mut candidate = Assignment::new();
        for (symbol, name, sort) in arena.symbols() {
            match name {
                "i" => candidate.set(symbol, Value::Bv { width: 4, value: 1 }),
                "j" => candidate.set(symbol, Value::Bv { width: 4, value: 2 }),
                "v" => candidate.set(symbol, Value::Bv { width: 8, value: 9 }),
                "y" => candidate.set(symbol, Value::Bv { width: 8, value: 7 }),
                "p" => candidate.set(symbol, Value::Bool(false)),
                _ if sort == Sort::BitVec(4) => {
                    candidate.set(symbol, Value::Bv { width: 4, value: 0 });
                }
                _ if sort == Sort::BitVec(8) => {
                    candidate.set(symbol, Value::Bv { width: 8, value: 0 });
                }
                _ => {}
            }
        }

        let originals = [y_eq_read, branch_assertion];
        let mut projected = complete_assignment(&arena, &candidate);
        let base_value = default_value_for_symbol(&arena, *a_symbol).unwrap();
        let initially_stored = store_value(
            &base_value,
            Value::Bv { width: 4, value: 2 },
            Value::Bv { width: 8, value: 9 },
        )
        .unwrap();
        projected.set(*b_symbol, initially_stored);
        assert_eq!(
            eval(&arena, branch_assertion, &projected).unwrap(),
            Value::Bool(true),
            "the store-definition branch should start true"
        );

        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected the inherited direct select equality to fail before repair");
        assert_eq!(failure.conjunct_term, y_eq_read);

        let stats = repair_projected_replay_failure(&arena, &originals, &mut projected, &failure)
            .unwrap()
            .expect("expected targeted store-chain select repair to change the projection");
        assert_eq!(stats.array_changes, 1);
        assert_eq!(stats.branch_symbol_changes, 1);

        let repaired_a = projected.get(*a_symbol).expect("repaired base array");
        assert_eq!(
            select_value(&repaired_a, &Value::Bv { width: 4, value: 1 }).unwrap(),
            Value::Bv { width: 8, value: 7 }
        );
        assert_eq!(
            first_projected_replay_failure(
                &arena,
                &originals,
                &projected,
                ProjectionRepairStats::default(),
            )
            .unwrap(),
            None
        );
        for &original in &originals {
            assert_eq!(
                eval(&arena, original, &projected).unwrap(),
                Value::Bool(true)
            );
        }
    }

    #[test]
    fn lazy_ext_branch_equality_repairs_target_through_store_definition() {
        let mut arena = TermArena::new();
        let base = arena.array_var("base", 4, 8).unwrap();
        let a = arena.array_var("a", 4, 8).unwrap();
        let b = arena.array_var("b", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let j = arena.bv_var("j", 4).unwrap();
        let v = arena.bv_var("v", 8).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let p = arena.bool_var("p").unwrap();
        let q = arena.bool_var("q").unwrap();
        let seven = arena.bv_const(8, 7).unwrap();
        let stored = arena.store(base, j, v).unwrap();
        let a_eq_store = arena.eq(a, stored).unwrap();
        let lower_branch = arena.or(a_eq_store, p).unwrap();
        let b_eq_a = arena.eq(b, a).unwrap();
        let equality_branch = arena.or(b_eq_a, q).unwrap();
        let read_b_i = arena.select(b, i).unwrap();
        let y_eq_read = arena.eq(y, read_b_i).unwrap();
        let y_eq_seven = arena.eq(y, seven).unwrap();

        let TermNode::Symbol(base_symbol) = arena.node(base) else {
            panic!("base should be a symbol");
        };
        let TermNode::Symbol(a_symbol) = arena.node(a) else {
            panic!("a should be a symbol");
        };
        let TermNode::Symbol(b_symbol) = arena.node(b) else {
            panic!("b should be a symbol");
        };

        let mut candidate = Assignment::new();
        for (symbol, name, sort) in arena.symbols() {
            match name {
                "i" => candidate.set(symbol, Value::Bv { width: 4, value: 1 }),
                "j" => candidate.set(symbol, Value::Bv { width: 4, value: 2 }),
                "v" => candidate.set(symbol, Value::Bv { width: 8, value: 9 }),
                "y" => candidate.set(symbol, Value::Bv { width: 8, value: 7 }),
                "p" | "q" => candidate.set(symbol, Value::Bool(false)),
                _ if sort == Sort::BitVec(4) => {
                    candidate.set(symbol, Value::Bv { width: 4, value: 0 });
                }
                _ if sort == Sort::BitVec(8) => {
                    candidate.set(symbol, Value::Bv { width: 8, value: 0 });
                }
                _ => {}
            }
        }

        let mut projected = complete_assignment(&arena, &candidate);
        let base_value = default_value_for_symbol(&arena, *base_symbol).unwrap();
        let a_initial = store_value(
            &base_value,
            Value::Bv { width: 4, value: 2 },
            Value::Bv { width: 8, value: 9 },
        )
        .unwrap();
        let b_desired = store_value(
            &a_initial,
            Value::Bv { width: 4, value: 1 },
            Value::Bv { width: 8, value: 7 },
        )
        .unwrap();
        projected.set(*a_symbol, a_initial);
        projected.set(*b_symbol, b_desired);
        assert_eq!(
            eval(&arena, lower_branch, &projected).unwrap(),
            Value::Bool(true),
            "the selected store definition should start true"
        );
        assert_eq!(
            eval(&arena, equality_branch, &projected).unwrap(),
            Value::Bool(false),
            "the branch equality should be the only initial failure"
        );

        let originals = [equality_branch, lower_branch, y_eq_read, y_eq_seven];
        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected the branch equality to fail before repair");
        assert_eq!(failure.conjunct_term, equality_branch);

        let stats = repair_projected_replay_failure(&arena, &originals, &mut projected, &failure)
            .unwrap()
            .expect("expected branch equality repair through the store definition");
        assert!(stats.changes() > 0);

        let repaired_base = projected.get(*base_symbol).expect("repaired base array");
        assert_eq!(
            select_value(&repaired_base, &Value::Bv { width: 4, value: 1 }).unwrap(),
            Value::Bv { width: 8, value: 7 }
        );
        assert!(
            first_projected_replay_failure(
                &arena,
                &originals,
                &projected,
                ProjectionRepairStats::default(),
            )
            .unwrap()
            .is_none()
        );
        for &original in &originals {
            assert_eq!(
                eval(&arena, original, &projected).unwrap(),
                Value::Bool(true)
            );
        }
    }

    #[test]
    fn lazy_ext_targeted_replay_can_choose_non_best_repairable_branch() {
        let mut arena = TermArena::new();
        let q = arena.bool_var("q").unwrap();
        let x = arena.int_var("x").unwrap();
        let y = arena.int_var("y").unwrap();
        let one = arena.int_const(1);
        let two = arena.int_const(2);
        let x_eq_one = arena.eq(x, one).unwrap();
        let y_eq_two = arena.eq(y, two).unwrap();
        let repairable_branch = arena.and(x_eq_one, y_eq_two).unwrap();
        let branch_assertion = arena.or(q, repairable_branch).unwrap();

        let TermNode::Symbol(q_symbol) = arena.node(q) else {
            panic!("q should be a symbol");
        };
        let TermNode::Symbol(x_symbol) = arena.node(x) else {
            panic!("x should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };

        let mut candidate = Assignment::new();
        candidate.set(*q_symbol, Value::Bool(false));
        candidate.set(*x_symbol, Value::Int(0));
        candidate.set(*y_symbol, Value::Int(0));

        let originals = [branch_assertion];
        let projected = complete_assignment(&arena, &candidate);
        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected the branch disjunction to fail before targeted repair");
        let or_failure = failure
            .failed_or
            .as_ref()
            .expect("expected branch failure details");
        assert_eq!(or_failure.best_branch_ordinal, 0);
        assert_eq!(or_failure.best_branch_term, q);
        assert_eq!(or_failure.best_branch_false_literals, 1);

        let ctx = RowCtx::default();
        let ExtReplay::Sat(model) =
            project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
        else {
            panic!("expected targeted replay to choose the repairable non-best branch");
        };
        let assignment = model.to_assignment();
        assert_eq!(assignment.get(*q_symbol), Some(Value::Bool(false)));
        assert_eq!(assignment.get(*x_symbol), Some(Value::Int(1)));
        assert_eq!(assignment.get(*y_symbol), Some(Value::Int(2)));
        assert_eq!(
            eval(&arena, branch_assertion, &assignment).unwrap(),
            Value::Bool(true)
        );
    }

    #[test]
    fn lazy_ext_targeted_replay_repairs_order_guarded_branch_choice() {
        let mut arena = TermArena::new();
        let q = arena.bool_var("q").unwrap();
        let x = arena.int_var("x").unwrap();
        let y = arena.int_var("y").unwrap();
        let z = arena.int_var("z").unwrap();
        let x_le_y = arena.int_le(x, y).unwrap();
        let x_gt_y = arena.not(x_le_y).unwrap();
        let z_eq_x = arena.eq(z, x).unwrap();
        let guarded_branch = arena.and(x_gt_y, z_eq_x).unwrap();
        let branch_assertion = arena.or(q, guarded_branch).unwrap();

        let TermNode::Symbol(q_symbol) = arena.node(q) else {
            panic!("q should be a symbol");
        };
        let TermNode::Symbol(x_symbol) = arena.node(x) else {
            panic!("x should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };
        let TermNode::Symbol(z_symbol) = arena.node(z) else {
            panic!("z should be a symbol");
        };

        let mut candidate = Assignment::new();
        candidate.set(*q_symbol, Value::Bool(false));
        candidate.set(*x_symbol, Value::Int(0));
        candidate.set(*y_symbol, Value::Int(0));
        candidate.set(*z_symbol, Value::Int(2));

        let originals = [branch_assertion];
        let projected = complete_assignment(&arena, &candidate);
        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected the branch disjunction to fail before targeted repair");
        let or_failure = failure
            .failed_or
            .as_ref()
            .expect("expected branch failure details");
        assert_eq!(or_failure.best_branch_ordinal, 0);
        assert_eq!(or_failure.best_branch_false_literals, 1);

        let ctx = RowCtx::default();
        let ExtReplay::Sat(model) =
            project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
        else {
            panic!("expected targeted replay to repair the order-guarded branch");
        };
        let assignment = model.to_assignment();
        assert_eq!(assignment.get(*q_symbol), Some(Value::Bool(false)));
        let Some(Value::Int(x_value)) = assignment.get(*x_symbol) else {
            panic!("x should have an integer value");
        };
        let Some(Value::Int(y_value)) = assignment.get(*y_symbol) else {
            panic!("y should have an integer value");
        };
        assert!(x_value > y_value);
        assert_eq!(assignment.get(*z_symbol), Some(Value::Int(x_value)));
        assert_eq!(
            eval(&arena, branch_assertion, &assignment).unwrap(),
            Value::Bool(true)
        );
    }

    #[test]
    fn lazy_ext_projection_repairs_supported_branch_array_equality() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let b = arena.array_var("b", 4, 8).unwrap();
        let j = arena.bv_var("j", 4).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let z = arena.bv_var("z", 8).unwrap();
        let p = arena.bool_var("p").unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let branch_assertion = arena.or(a_eq_b, p).unwrap();
        let read_a_j = arena.select(a, j).unwrap();
        let y_eq_a_read = arena.eq(y, read_a_j).unwrap();
        let read_b_j = arena.select(b, j).unwrap();
        let z_eq_b_read = arena.eq(z, read_b_j).unwrap();

        let TermNode::Symbol(a_symbol) = arena.node(a) else {
            panic!("a should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };
        let TermNode::Symbol(z_symbol) = arena.node(z) else {
            panic!("z should be a symbol");
        };

        let mut ctx = RowCtx::default();
        ctx.sites.push(RowSite {
            fresh: *y_symbol,
            index: j,
            kind: RowKind::Var { array: *a_symbol },
        });

        let mut candidate = Assignment::new();
        for (symbol, name, sort) in arena.symbols() {
            match name {
                "j" => candidate.set(symbol, Value::Bv { width: 4, value: 1 }),
                "y" => candidate.set(symbol, Value::Bv { width: 8, value: 9 }),
                "z" => candidate.set(symbol, Value::Bv { width: 8, value: 0 }),
                "p" => candidate.set(symbol, Value::Bool(false)),
                _ if sort == Sort::BitVec(4) => {
                    candidate.set(symbol, Value::Bv { width: 4, value: 0 });
                }
                _ if sort == Sort::BitVec(8) => {
                    candidate.set(symbol, Value::Bv { width: 8, value: 0 });
                }
                _ => {}
            }
        }

        let originals = [branch_assertion, y_eq_a_read, z_eq_b_read];
        let ExtReplay::Sat(model) =
            project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
        else {
            panic!("expected branch array-equality repair to replay");
        };
        let assignment = model.to_assignment();
        assert_eq!(
            assignment.get(*z_symbol),
            Some(Value::Bv { width: 8, value: 9 })
        );
        for &original in &originals {
            assert_eq!(
                eval(&arena, original, &assignment).unwrap(),
                Value::Bool(true)
            );
        }
    }

    #[test]
    fn lazy_ext_projection_repairs_selected_array_equality_component() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let b = arena.array_var("b", 4, 8).unwrap();
        let c = arena.array_var("c", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let k0 = arena.bv_var("k0", 4).unwrap();
        let k2 = arena.bv_var("k2", 4).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let p = arena.bool_var("p").unwrap();
        let q = arena.bool_var("q").unwrap();
        let two = arena.bv_const(8, 2).unwrap();
        let c_eq_b = arena.eq(c, b).unwrap();
        let b_eq_a = arena.eq(b, a).unwrap();
        let c_branch = arena.or(c_eq_b, p).unwrap();
        let b_branch = arena.or(b_eq_a, q).unwrap();
        let read_b_i = arena.select(b, i).unwrap();
        let y_eq_read_b = arena.eq(y, read_b_i).unwrap();
        let y_eq_two = arena.eq(y, two).unwrap();

        let a_symbol = match arena.node(a) {
            TermNode::Symbol(symbol) => *symbol,
            _ => panic!("a should be a symbol"),
        };
        let b_symbol = match arena.node(b) {
            TermNode::Symbol(symbol) => *symbol,
            _ => panic!("b should be a symbol"),
        };
        let c_symbol = match arena.node(c) {
            TermNode::Symbol(symbol) => *symbol,
            _ => panic!("c should be a symbol"),
        };
        let y_symbol = match arena.node(y) {
            TermNode::Symbol(symbol) => *symbol,
            _ => panic!("y should be a symbol"),
        };

        let mut ctx = RowCtx::default();
        let c_at_k0 = ctx.fresh_symbol(&mut arena, Sort::BitVec(8)).unwrap();
        let c_at_k2 = ctx.fresh_symbol(&mut arena, Sort::BitVec(8)).unwrap();
        ctx.sites.push(RowSite {
            fresh: y_symbol,
            index: i,
            kind: RowKind::Var { array: b_symbol },
        });
        ctx.sites.push(RowSite {
            fresh: c_at_k0,
            index: k0,
            kind: RowKind::Var { array: c_symbol },
        });
        ctx.sites.push(RowSite {
            fresh: c_at_k2,
            index: k2,
            kind: RowKind::Var { array: c_symbol },
        });

        let mut candidate = Assignment::new();
        for (symbol, name, sort) in arena.symbols() {
            match name {
                "i" => candidate.set(symbol, Value::Bv { width: 4, value: 1 }),
                "k0" => candidate.set(symbol, Value::Bv { width: 4, value: 0 }),
                "k2" => candidate.set(symbol, Value::Bv { width: 4, value: 2 }),
                "y" => candidate.set(symbol, Value::Bv { width: 8, value: 2 }),
                "p" | "q" => candidate.set(symbol, Value::Bool(false)),
                _ if symbol == c_at_k0 || symbol == c_at_k2 => {
                    candidate.set(symbol, Value::Bv { width: 8, value: 3 });
                }
                _ if sort == Sort::BitVec(4) => {
                    candidate.set(symbol, Value::Bv { width: 4, value: 0 });
                }
                _ if sort == Sort::BitVec(8) => {
                    candidate.set(symbol, Value::Bv { width: 8, value: 0 });
                }
                _ => {}
            }
        }

        let arrays =
            collect_base_array_entries(&arena, &ctx, &candidate, "test projection").unwrap();
        let mut projected = complete_assignment(&arena, &candidate);
        for (&array, entries) in &arrays {
            projected.set(
                array,
                array_value_from_entries(&arena, array, entries).unwrap(),
            );
        }

        let originals = [c_branch, b_branch, y_eq_read_b, y_eq_two];
        let failure = first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected the component carry branch to fail before repair");
        assert_eq!(failure.conjunct_term, c_branch);
        let stats = repair_projected_replay_failure(&arena, &originals, &mut projected, &failure)
            .unwrap()
            .expect("expected component array-equality repair to change the projection");
        assert!(stats.branch_symbol_changes >= 2);
        assert!(
            first_projected_replay_failure(
                &arena,
                &originals,
                &projected,
                ProjectionRepairStats::default(),
            )
            .unwrap()
            .is_none()
        );

        let a_value = projected.get(a_symbol).expect("a value");
        let b_value = projected.get(b_symbol).expect("b value");
        let c_value = projected.get(c_symbol).expect("c value");
        assert_eq!(a_value, b_value);
        assert_eq!(b_value, c_value);
        assert_eq!(
            projected.get(y_symbol),
            Some(Value::Bv { width: 8, value: 2 })
        );
        for &original in &originals {
            assert_eq!(
                eval(&arena, original, &projected).unwrap(),
                Value::Bool(true)
            );
        }
    }

    #[test]
    fn lazy_ext_projection_repairs_multi_literal_branch_schedule() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let b = arena.array_var("b", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let j = arena.bv_var("j", 4).unwrap();
        let v = arena.bv_var("v", 8).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let z = arena.bv_var("z", 8).unwrap();
        let q = arena.bool_var("q").unwrap();
        let r = arena.bool_var("r").unwrap();
        let s = arena.bool_var("s").unwrap();

        let i_eq_j = arena.eq(i, j).unwrap();
        let stored = arena.store(a, i, v).unwrap();
        let b_eq_store = arena.eq(b, stored).unwrap();
        let wanted_branch = arena.and(i_eq_j, b_eq_store).unwrap();
        let r_and_s = arena.and(r, s).unwrap();
        let noisy_alt = arena.and(q, r_and_s).expect("alternate branch");
        let branch_assertion = arena.or(wanted_branch, noisy_alt).unwrap();
        let read_a_j = arena.select(a, j).unwrap();
        let y_eq_a_read = arena.eq(y, read_a_j).unwrap();
        let read_b_j = arena.select(b, j).unwrap();
        let z_eq_b_read = arena.eq(z, read_b_j).unwrap();

        let TermNode::Symbol(a_symbol) = arena.node(a) else {
            panic!("a should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };
        let TermNode::Symbol(z_symbol) = arena.node(z) else {
            panic!("z should be a symbol");
        };

        let mut ctx = RowCtx::default();
        ctx.sites.push(RowSite {
            fresh: *y_symbol,
            index: j,
            kind: RowKind::Var { array: *a_symbol },
        });

        let mut candidate = Assignment::new();
        for (symbol, name, sort) in arena.symbols() {
            match name {
                "i" => candidate.set(symbol, Value::Bv { width: 4, value: 0 }),
                "j" => candidate.set(symbol, Value::Bv { width: 4, value: 1 }),
                "v" => candidate.set(symbol, Value::Bv { width: 8, value: 9 }),
                "y" => candidate.set(symbol, Value::Bv { width: 8, value: 5 }),
                "z" => candidate.set(symbol, Value::Bv { width: 8, value: 0 }),
                "q" | "r" | "s" => candidate.set(symbol, Value::Bool(false)),
                _ if sort == Sort::BitVec(4) => {
                    candidate.set(symbol, Value::Bv { width: 4, value: 0 });
                }
                _ if sort == Sort::BitVec(8) => {
                    candidate.set(symbol, Value::Bv { width: 8, value: 0 });
                }
                _ => {}
            }
        }

        let originals = [branch_assertion, y_eq_a_read, z_eq_b_read];
        let ExtReplay::Sat(model) =
            project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
        else {
            panic!("expected multi-literal branch repair to replay");
        };
        let assignment = model.to_assignment();
        assert_eq!(
            assignment.get(*z_symbol),
            Some(Value::Bv { width: 8, value: 9 })
        );
        for &original in &originals {
            assert_eq!(
                eval(&arena, original, &assignment).unwrap(),
                Value::Bool(true)
            );
        }
    }

    #[test]
    fn lazy_ext_projection_repairs_scalar_equality_by_replay_improvement() {
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let y = arena.int_var("y").unwrap();
        let one = arena.int_const(1);
        let y_eq_x = arena.eq(y, x).unwrap();
        let y_eq_one = arena.eq(y, one).unwrap();

        let TermNode::Symbol(x_symbol) = arena.node(x) else {
            panic!("x should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };

        let mut candidate = Assignment::new();
        candidate.set(*x_symbol, Value::Int(0));
        candidate.set(*y_symbol, Value::Int(1));

        let ctx = RowCtx::default();
        let originals = [y_eq_x, y_eq_one];
        let ExtReplay::Sat(model) =
            project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
        else {
            panic!("expected scalar equality repair to replay");
        };
        let assignment = model.to_assignment();
        assert_eq!(assignment.get(*x_symbol), Some(Value::Int(1)));
        assert_eq!(assignment.get(*y_symbol), Some(Value::Int(1)));
        for &original in &originals {
            assert_eq!(
                eval(&arena, original, &assignment).unwrap(),
                Value::Bool(true)
            );
        }
    }

    #[test]
    fn lazy_ext_projection_propagates_select_supported_scalar_equalities() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let x = arena.bv_var("x", 8).unwrap();
        let z = arena.bv_var("z", 8).unwrap();
        let seven = arena.bv_const(8, 7).unwrap();
        let read = arena.select(a, i).unwrap();
        let y_eq_read = arena.eq(y, read).unwrap();
        let y_eq_seven = arena.eq(y, seven).unwrap();
        let x_eq_y = arena.eq(x, y).unwrap();
        let x_eq_z = arena.eq(x, z).unwrap();
        let z_eq_y = arena.eq(z, y).unwrap();

        let TermNode::Symbol(array) = arena.node(a) else {
            panic!("array should be a symbol");
        };
        let TermNode::Symbol(y_symbol) = arena.node(y) else {
            panic!("y should be a symbol");
        };
        let TermNode::Symbol(x_symbol) = arena.node(x) else {
            panic!("x should be a symbol");
        };
        let TermNode::Symbol(z_symbol) = arena.node(z) else {
            panic!("z should be a symbol");
        };

        let mut ctx = RowCtx::default();
        ctx.sites.push(RowSite {
            fresh: *y_symbol,
            index: i,
            kind: RowKind::Var { array: *array },
        });

        let mut candidate = Assignment::new();
        for (symbol, name, sort) in arena.symbols() {
            match name {
                "i" => candidate.set(symbol, Value::Bv { width: 4, value: 0 }),
                "y" => candidate.set(symbol, Value::Bv { width: 8, value: 7 }),
                "x" | "z" => candidate.set(symbol, Value::Bv { width: 8, value: 0 }),
                _ if sort == Sort::BitVec(4) => {
                    candidate.set(symbol, Value::Bv { width: 4, value: 0 });
                }
                _ if sort == Sort::BitVec(8) => {
                    candidate.set(symbol, Value::Bv { width: 8, value: 0 });
                }
                _ => {}
            }
        }

        let originals = [y_eq_read, y_eq_seven, x_eq_y, x_eq_z, z_eq_y];
        let ExtReplay::Sat(model) =
            project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
        else {
            panic!("expected select-supported scalar propagation to replay");
        };
        let assignment = model.to_assignment();
        assert_eq!(
            assignment.get(*x_symbol),
            Some(Value::Bv { width: 8, value: 7 })
        );
        assert_eq!(
            assignment.get(*z_symbol),
            Some(Value::Bv { width: 8, value: 7 })
        );
        for &original in &originals {
            assert_eq!(
                eval(&arena, original, &assignment).unwrap(),
                Value::Bool(true)
            );
        }
    }

    #[test]
    fn lazy_ext_projection_prefers_asserted_select_equalities() {
        // Timeout salvage must not let auxiliary extensionality reads overwrite
        // an original select equality in the projected array model. The final
        // full replay remains the soundness gate; this only chooses the candidate
        // array entry that the original formula explicitly demands.
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let j = arena.bv_var("j", 4).unwrap();
        let x = arena.bv_var("x", 8).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let read = arena.select(a, i).unwrap();
        let other_read = arena.select(a, j).unwrap();
        let x_read = arena.eq(x, read).unwrap();
        let y_read = arena.eq(y, other_read).unwrap();
        let i_eq_j = arena.eq(i, j).unwrap();

        let TermNode::Symbol(array) = arena.node(a) else {
            panic!("array variable should be a symbol");
        };
        let array = *array;

        let mut ctx = RowCtx::default();
        let demanded = ctx.fresh_symbol(&mut arena, Sort::BitVec(8)).unwrap();
        let same_index = ctx.fresh_symbol(&mut arena, Sort::BitVec(8)).unwrap();
        let auxiliary = ctx.fresh_symbol(&mut arena, Sort::BitVec(8)).unwrap();
        ctx.sites.push(RowSite {
            fresh: demanded,
            index: i,
            kind: RowKind::Var { array },
        });
        ctx.sites.push(RowSite {
            fresh: same_index,
            index: j,
            kind: RowKind::Var { array },
        });
        ctx.sites.push(RowSite {
            fresh: auxiliary,
            index: i,
            kind: RowKind::Var { array },
        });

        let mut candidate = Assignment::new();
        for (symbol, name, sort) in arena.symbols() {
            if name == "i" || name == "j" {
                candidate.set(symbol, Value::Bv { width: 4, value: 0 });
            } else if name == "x" {
                candidate.set(symbol, Value::Bv { width: 8, value: 7 });
            } else if name == "y" {
                candidate.set(symbol, Value::Bv { width: 8, value: 3 });
            } else if symbol == demanded {
                candidate.set(symbol, Value::Bv { width: 8, value: 7 });
            } else if symbol == same_index {
                candidate.set(symbol, Value::Bv { width: 8, value: 3 });
            } else if symbol == auxiliary {
                candidate.set(symbol, Value::Bv { width: 8, value: 0 });
            } else if sort == Sort::BitVec(4) {
                candidate.set(symbol, Value::Bv { width: 4, value: 0 });
            } else if sort == Sort::BitVec(8) {
                candidate.set(symbol, Value::Bv { width: 8, value: 0 });
            }
        }

        let originals = [x_read, y_read, i_eq_j];
        let ExtReplay::Sat(model) =
            project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
        else {
            panic!("expected repaired projection to replay");
        };
        let assignment = model.to_assignment();
        for &original in &originals {
            assert_eq!(
                eval(&arena, original, &assignment).unwrap(),
                Value::Bool(true)
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

    #[test]
    fn cross_store_array_refuter_closes_qf_ax_unsats_only() {
        for (tag, input) in [
            (
                "arrays0",
                include_str!(
                    "../../../corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean/cli__regress0__arrays__arrays0.smt2"
                ),
            ),
            (
                "arrays4",
                include_str!(
                    "../../../corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean/cli__regress0__arrays__arrays4.smt2"
                ),
            ),
        ] {
            let script = parse_script(input).unwrap_or_else(|error| panic!("{tag}: {error}"));
            let cert = cross_store_array_disequality_refutation(&script.arena, &script.assertions)
                .unwrap_or_else(|| panic!("{tag}: expected cross-store certificate"));
            assert!(
                cert.recheck(&script.arena, &script.assertions),
                "{tag}: cross-store certificate must recheck"
            );
            assert!(
                prove_unsat_by_symmetric_swap_chain(&script.arena, &script.assertions),
                "expected structural cross-store refuter to close {tag}"
            );
        }

        let sat_script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean/cli__regress0__arrays__arrays3.smt2"
        ))
        .unwrap();
        assert!(
            cross_store_array_disequality_refutation(&sat_script.arena, &sat_script.assertions)
                .is_none(),
            "arrays3 is SAT and must not produce a cross-store certificate"
        );
        assert!(
            !prove_unsat_by_symmetric_swap_chain(&sat_script.arena, &sat_script.assertions),
            "arrays3 is SAT and must not match the same-index cross-store refuter"
        );
    }

    #[test]
    fn const_array_default_mismatch_certificate_rechecks_constarr3() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_ALIA/cvc5-regress-clean/cli__regress1__constarr3.smt2"
        ))
        .unwrap();

        let cert = const_array_default_mismatch_refutation(&script.arena, &script.assertions)
            .expect("constarr3 has finite writes over different constant defaults");
        assert_eq!(cert.lhs_writes, 1);
        assert_eq!(cert.rhs_writes, 1);
        assert!(
            cert.recheck(&script.arena, &script.assertions),
            "certificate must rederive from the original assertions"
        );
    }

    #[test]
    fn store_chain_readback_certificate_rechecks_ios_np_sf() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_ALIA/cvc5-regress-clean/cli__regress0__proofs__ios_np_sf.smt2"
        ))
        .unwrap();

        let cert = store_chain_readback_refutation(&script.arena, &script.assertions)
            .expect("ios_np_sf has a finite store-chain readback contradiction");
        assert_eq!(cert.write_side, StoreChainSide::Left);
        assert_eq!(cert.lhs_writes, 3);
        assert_eq!(cert.rhs_writes, 3);
        assert!(
            cert.recheck(&script.arena, &script.assertions),
            "certificate must rederive from the original assertions"
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
