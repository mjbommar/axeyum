//! First-class `QF_UFBV` solving by eager Ackermann elimination (ADR-0013).
//!
//! [`check_with_function_elimination`] is the consumer-facing entry point for
//! queries that use uninterpreted-function applications: it eagerly eliminates
//! functions to `QF_BV` by Ackermann congruence reduction, solves the result
//! with any [`SolverBackend`], and on `sat` projects the model back to function
//! interpretations and replays it against the original assertions with the
//! ground evaluator. Pure `QF_BV` queries pass straight through unchanged.

use std::collections::HashSet;

use axeyum_ir::{Assignment, FuncId, TermArena, TermId, Value, eval};
use axeyum_rewrite::{FuncElimError, eliminate_functions};

use crate::backend::{CheckResult, SolverBackend, SolverConfig, SolverError};
use crate::model::Model;

/// Checks a (possibly function-using) `QF_UFBV` conjunction with `backend`.
///
/// Uninterpreted functions are eliminated to `QF_BV` by Ackermann congruence
/// reduction; a `sat` model is projected back to function interpretations and
/// replayed against the original assertions, so the returned [`Model`] is over
/// the original query (carrying both symbol values and function
/// interpretations).
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for constructs outside the supported
/// fragment, or [`SolverError`] from the backend. A `sat` model that fails to
/// replay is a [`SolverError::Backend`].
pub fn check_with_function_elimination<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let elimination = eliminate_functions(arena, assertions).map_err(map_elim_error)?;
    let eliminated = elimination.assertions().to_vec();
    let result = backend.check(arena, &eliminated, config)?;

    let CheckResult::Sat(model) = result else {
        return Ok(result);
    };

    let assignment = model.to_assignment();
    project_replay_build(arena, &elimination, assertions, &assignment)
}

/// Projects a candidate model back to function interpretations, replays it
/// against the original `assertions`, and builds the output [`Model`] over the
/// original query — the shared `sat` tail of both the eager and lazy entry
/// points.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] if model projection fails or if any original
/// assertion fails to replay to `true` under the projected model.
fn project_replay_build(
    arena: &TermArena,
    elimination: &axeyum_rewrite::FunctionElimination,
    assertions: &[TermId],
    assignment: &Assignment,
) -> Result<CheckResult, SolverError> {
    let projected = elimination
        .project_model(arena, assignment)
        .map_err(|error| {
            SolverError::Backend(format!("function model projection failed: {error}"))
        })?;

    for &assertion in assertions {
        match eval(arena, assertion, &projected) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Err(SolverError::Backend(format!(
                    "function sat model replay failed: assertion #{} evaluated to false",
                    assertion.index()
                )));
            }
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "function sat model replay failed: assertion #{} evaluated to non-Boolean {value}",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "function sat model replay failed: assertion #{} failed evaluation: {error}",
                    assertion.index()
                )));
            }
        }
    }

    // Build a model over the original query (drop the internal fresh
    // application variables) carrying both symbol values and reconstructed
    // function interpretations.
    let mut out = Model::new();
    for (symbol, name, _sort) in arena.symbols() {
        if name.starts_with("!fn_app_") {
            continue;
        }
        if let Some(value) = projected.get(symbol) {
            out.set(symbol, value);
        }
    }
    for (func, _name, _params, _result) in arena.functions() {
        if let Some(interp) = projected.function(func) {
            out.set_function(func, interp.clone());
        }
    }
    Ok(CheckResult::Sat(out))
}

/// Lazy/on-demand Ackermann for `QF_UFBV` (P1.6): abstracts each uninterpreted
/// application as a fresh variable, solves the abstraction, and adds a
/// functional-consistency lemma `(⋀ args_i = args_j) => fresh_i = fresh_j` ONLY
/// for an application pair a candidate model actually violates (equal argument
/// tuples, unequal results), re-solving until the model is functionally
/// consistent or the abstraction is UNSAT.
///
/// This is a CEGAR refinement of the eager [`check_with_function_elimination`]:
/// instead of asserting a congruence lemma for every pair of same-function
/// applications up front, it starts from the abstraction (the relaxation with no
/// lemmas) and refines only on observed violations. The abstraction is a
/// relaxation (strictly fewer constraints), so an UNSAT abstraction soundly
/// witnesses UNSAT of the original; a functionally-consistent `sat` model
/// projects, replays, and is returned over the original query exactly as in the
/// eager path.
///
/// Termination: there are finitely many application pairs and each lemma is
/// added at most once (tracked by index pair), so the loop adds at most
/// `O(applications²)` lemmas before either deciding UNSAT or returning a
/// consistent model.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for constructs outside the supported
/// `QF_UFBV` fragment, or [`SolverError`] from the backend. A consistent `sat`
/// model that fails to replay against the original assertions is a
/// [`SolverError::Backend`].
pub fn check_qf_ufbv_lazy<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let elim = eliminate_functions(arena, assertions).map_err(map_elim_error)?;
    if !elim.had_functions() {
        // No uninterpreted functions: nothing to abstract, solve directly.
        return backend.check(arena, assertions, config);
    }

    // The application metadata is borrowed from `arena` (the arg slices), so
    // snapshot it into owned data before we start mutating `arena` with lemmas.
    let applications: Vec<(FuncId, Vec<TermId>, axeyum_ir::SymbolId)> = elim
        .applications()
        .into_iter()
        .map(|(func, args, fresh)| (func, args.to_vec(), fresh))
        .collect();

    // Group application indices by function, preserving discovery order.
    let mut groups: Vec<(FuncId, Vec<usize>)> = Vec::new();
    for (idx, (func, _args, _fresh)) in applications.iter().enumerate() {
        if let Some((_, members)) = groups.iter_mut().find(|(g, _)| g == func) {
            members.push(idx);
        } else {
            groups.push((*func, vec![idx]));
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
        for (_func, members) in &groups {
            for a in 0..members.len() {
                for b in (a + 1)..members.len() {
                    let i = members[a];
                    let j = members[b];
                    let (_fi, args_i, fresh_i) = &applications[i];
                    let (_fj, args_j, fresh_j) = &applications[j];
                    if args_i.len() != args_j.len() {
                        continue;
                    }
                    if added.contains(&(i, j)) {
                        continue;
                    }
                    if args_tuples_equal(arena, args_i, args_j, &assignment)?
                        && results_differ(&assignment, *fresh_i, *fresh_j)
                    {
                        new_lemmas.push((i, j));
                    }
                }
            }
        }

        if new_lemmas.is_empty() {
            // Model is functionally consistent: project, replay, and return.
            return project_replay_build(arena, &elim, assertions, &assignment);
        }

        for (i, j) in new_lemmas {
            let lemma = congruence_lemma(
                arena,
                &applications[i].1,
                &applications[j].1,
                applications[i].2,
                applications[j].2,
            )?;
            working.push(lemma);
            added.insert((i, j));
        }
    }
}

/// Whether every argument of two applications evaluates to the same scalar code
/// under `assignment`.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] if an argument term fails to evaluate.
fn args_tuples_equal(
    arena: &TermArena,
    args_i: &[TermId],
    args_j: &[TermId],
    assignment: &Assignment,
) -> Result<bool, SolverError> {
    for (&a, &b) in args_i.iter().zip(args_j) {
        let va = eval(arena, a, assignment)
            .map_err(|error| SolverError::Backend(format!("lazy congruence eval failed: {error}")))?
            .scalar_code();
        let vb = eval(arena, b, assignment)
            .map_err(|error| SolverError::Backend(format!("lazy congruence eval failed: {error}")))?
            .scalar_code();
        if va != vb {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Whether the two fresh result symbols hold different values under `assignment`
/// (an unassigned symbol is treated as a non-match, conservatively no
/// violation).
fn results_differ(
    assignment: &Assignment,
    fresh_i: axeyum_ir::SymbolId,
    fresh_j: axeyum_ir::SymbolId,
) -> bool {
    match (assignment.get(fresh_i), assignment.get(fresh_j)) {
        (Some(vi), Some(vj)) => vi.scalar_code() != vj.scalar_code(),
        _ => false,
    }
}

/// Builds the functional-consistency lemma
/// `(⋀_k args_i[k] = args_j[k]) => (fresh_i = fresh_j)` over the fresh result
/// symbols of two same-function applications.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] if an IR builder fails.
fn congruence_lemma(
    arena: &mut TermArena,
    args_i: &[TermId],
    args_j: &[TermId],
    fresh_i: axeyum_ir::SymbolId,
    fresh_j: axeyum_ir::SymbolId,
) -> Result<TermId, SolverError> {
    let mut same_args: Option<TermId> = None;
    for (&a, &b) in args_i.iter().zip(args_j) {
        let eq = arena.eq(a, b).map_err(|error| {
            SolverError::Backend(format!("lazy congruence build failed: {error}"))
        })?;
        same_args = Some(match same_args {
            Some(acc) => arena
                .and(acc, eq)
                .map_err(|e| SolverError::Backend(format!("lazy congruence build failed: {e}")))?,
            None => eq,
        });
    }
    let var_i = arena.var(fresh_i);
    let var_j = arena.var(fresh_j);
    let same_result = arena
        .eq(var_i, var_j)
        .map_err(|error| SolverError::Backend(format!("lazy congruence build failed: {error}")))?;
    match same_args {
        Some(guard) => arena.implies(guard, same_result).map_err(|error| {
            SolverError::Backend(format!("lazy congruence build failed: {error}"))
        }),
        // A zero-arity application has a single tuple, so distinct applications
        // of it cannot both exist; defensively, assert equality unguarded.
        None => Ok(same_result),
    }
}

fn map_elim_error(error: FuncElimError) -> SolverError {
    match error {
        FuncElimError::Unsupported(what) => SolverError::Unsupported(what),
        FuncElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    }
}

#[cfg(test)]
#[allow(clippy::many_single_char_names, clippy::similar_names)]
mod tests {
    use super::check_qf_ufbv_lazy;
    use crate::backend::{CheckResult, SolverConfig};
    use crate::combined::check_with_all_theories;
    use crate::lia::DEFAULT_INT_WIDTH;
    use crate::sat_bv_backend::SatBvBackend;
    use axeyum_ir::{Sort, TermArena, Value, eval};

    #[test]
    fn lazy_ufbv_refutes_congruence_violation() {
        // f(a) != f(b) AND a = b  over BV8  =>  UNSAT (a lemma is required to
        // refute: the abstraction alone is SAT).
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let fa_ne_fb = {
            let eq = arena.eq(fa, fb).unwrap();
            arena.not(eq).unwrap()
        };
        let a_eq_b = arena.eq(a, b).unwrap();

        let mut backend = SatBvBackend::new();
        let config = SolverConfig::default();
        let result =
            check_qf_ufbv_lazy(&mut backend, &mut arena, &[fa_ne_fb, a_eq_b], &config).unwrap();
        assert_eq!(result, CheckResult::Unsat);
    }

    #[test]
    fn lazy_ufbv_sat_model_replays() {
        // f(a) = c AND a = b  over BV8  =>  SAT, and the returned model replays.
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_const(8, 0x2a).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fa_eq_c = arena.eq(fa, c).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let originals = [fa_eq_c, a_eq_b];

        let mut backend = SatBvBackend::new();
        let config = SolverConfig::default();
        let result = check_qf_ufbv_lazy(&mut backend, &mut arena, &originals, &config).unwrap();
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
    fn lazy_ufbv_refutes_nested_application_congruence() {
        // f(f(a)) != a  AND  f(a) = a  over BV8. Here one application's argument is
        // itself an abstracted application: f(a) -> v1, f(f(a)) -> v2, with v1 = a
        // forced. The on-demand lemma (a = v1) => (v1 = v2) then forces v2 = a,
        // contradicting f(f(a)) != a. Exercises lazy Ackermann over nested apps.
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let a = arena.bv_var("a", 8).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let ffa = arena.apply(f, &[fa]).unwrap();
        let ffa_ne_a = {
            let eq = arena.eq(ffa, a).unwrap();
            arena.not(eq).unwrap()
        };
        let fa_eq_a = arena.eq(fa, a).unwrap();

        let mut backend = SatBvBackend::new();
        let config = SolverConfig::default();
        let result =
            check_qf_ufbv_lazy(&mut backend, &mut arena, &[ffa_ne_a, fa_eq_a], &config).unwrap();
        assert_eq!(result, CheckResult::Unsat);
    }

    #[test]
    fn lazy_ufbv_nested_application_sat_replays() {
        // f(f(a)) = a  AND  f(a) = b: satisfiable (an involution f with f(a)=b,
        // f(b)=a, a != b). The nested application must project to a coherent
        // function interpretation that replays.
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let ffa = arena.apply(f, &[fa]).unwrap();
        let ffa_eq_a = arena.eq(ffa, a).unwrap();
        let fa_eq_b = arena.eq(fa, b).unwrap();
        let originals = [ffa_eq_a, fa_eq_b];

        let mut backend = SatBvBackend::new();
        let config = SolverConfig::default();
        let CheckResult::Sat(model) =
            check_qf_ufbv_lazy(&mut backend, &mut arena, &originals, &config).unwrap()
        else {
            panic!("expected SAT for the involution");
        };
        let assignment = model.to_assignment();
        for &t in &originals {
            assert_eq!(
                eval(&arena, t, &assignment).unwrap(),
                Value::Bool(true),
                "nested-application sat model must replay"
            );
        }
    }

    #[test]
    fn lazy_ufbv_matches_eager_differential() {
        // ~300 deterministic-random small QF_UFBV formulas; the lazy verdict must
        // agree with the eager full-theory verdict whenever both decide.
        let config = SolverConfig::default();
        let mut jointly_decided = 0usize;
        let mut unsat_count = 0usize;

        // Simple LCG (no `rand` crate); seeded by a constant, varied per case.
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;

        for _case in 0..300usize {
            let mut arena = TermArena::new();
            let assertions = [build_case(&mut arena, &mut state)];

            let mut lazy_backend = SatBvBackend::new();
            let mut eager_backend = SatBvBackend::new();
            let lazy = check_qf_ufbv_lazy(&mut lazy_backend, &mut arena, &assertions, &config)
                .expect("lazy check");
            let eager = check_with_all_theories(
                &mut eager_backend,
                &mut arena,
                &assertions,
                DEFAULT_INT_WIDTH,
                &config,
            )
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

    /// Builds one deterministic-random small `QF_UFBV` formula over `BitVec(4)`
    /// vars and two unary functions, returning its single top-level assertion.
    fn build_case(arena: &mut TermArena, state: &mut u64) -> axeyum_ir::TermId {
        let w = 4u32;
        let f = arena
            .declare_fun("f", &[Sort::BitVec(w)], Sort::BitVec(w))
            .unwrap();
        let g = arena
            .declare_fun("g", &[Sort::BitVec(w)], Sort::BitVec(w))
            .unwrap();
        let x = arena.bv_var("x", w).unwrap();
        let y = arena.bv_var("y", w).unwrap();
        let z = arena.bv_var("z", w).unwrap();

        // Term pool: vars, a constant, f/g applications, and a couple of bv ops.
        let mut pool: Vec<axeyum_ir::TermId> = vec![x, y, z];
        pool.push(
            arena
                .bv_const(w, u128::from(next_rand(state) & 0xf))
                .unwrap(),
        );
        for _ in 0..3 {
            let pick = pool[(next_rand(state) as usize) % pool.len()];
            let app = match next_rand(state) % 2 {
                0 => arena.apply(f, &[pick]).unwrap(),
                _ => arena.apply(g, &[pick]).unwrap(),
            };
            pool.push(app);
        }
        for _ in 0..2 {
            let lhs = pool[(next_rand(state) as usize) % pool.len()];
            let rhs = pool[(next_rand(state) as usize) % pool.len()];
            let op = match next_rand(state) % 3 {
                0 => arena.bv_add(lhs, rhs).unwrap(),
                1 => arena.bv_and(lhs, rhs).unwrap(),
                _ => arena.bv_xor(lhs, rhs).unwrap(),
            };
            pool.push(op);
        }

        // A few eq/diseq atoms.
        let atom_count = 2 + (next_rand(state) % 3) as usize;
        let mut atoms: Vec<axeyum_ir::TermId> = Vec::with_capacity(atom_count);
        for _ in 0..atom_count {
            let lhs = pool[(next_rand(state) as usize) % pool.len()];
            let rhs = pool[(next_rand(state) as usize) % pool.len()];
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
