//! First-class `QF_ABV` solving by eager array elimination (ADR-0010).
//!
//! [`check_with_array_elimination`] is the consumer-facing entry point for
//! queries that use `select`/`store`: it eagerly eliminates arrays to `QF_BV`,
//! solves the result with any [`SolverBackend`], and on `sat` projects the
//! model back to array values and replays it against the original array
//! assertions with the ground evaluator. Pure `QF_BV` queries pass straight
//! through unchanged.

use std::collections::HashSet;

use axeyum_ir::{Assignment, SymbolId, TermArena, TermId, Value, eval};
use axeyum_rewrite::{ArrayElimError, ArrayElimination, eliminate_arrays};

use crate::backend::{CheckResult, SolverBackend, SolverConfig, SolverError};
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
