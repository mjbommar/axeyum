//! Integration tests for the online (model-based) `Nelson–Oppen` combination of
//! `EUF` + linear real arithmetic — `check_qf_uflra_online`.
//!
//! The load-bearing test is the **differential fuzz** against the trusted offline
//! decider `check_with_uf_arithmetic` (eager Ackermann): over many deterministic
//! random `QF_UFLRA` conjunctions the online combination must AGREE (sat / unsat)
//! with the offline decider on every jointly-decided instance — zero disagreements —
//! and every `sat` model must replay against the original assertions. A graceful
//! `Unknown` on a hard case is fine; a wrong sat / unsat is unacceptable.

use std::time::Duration;

use axeyum_ir::{Assignment, Rational, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, IncrementalDecision, SolverConfig, UnknownKind,
    check_qf_uflra_boolean_prop_metrics, check_qf_uflra_boolean_with_metrics,
    check_qf_uflra_online, check_with_uf_arithmetic, combined_incremental_structure,
    combined_incremental_vs_check, combined_theory_propagations,
};

fn rconst(arena: &mut TermArena, n: i128) -> TermId {
    arena.real_const(Rational::integer(n))
}

fn rvar(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, Sort::Real).expect("declare real");
    arena.var(s)
}

/// `Some(true)` for SAT, `Some(false)` for UNSAT, `None` for Unknown.
fn verdict(result: &CheckResult) -> Option<bool> {
    match result {
        CheckResult::Sat(_) => Some(true),
        CheckResult::Unsat => Some(false),
        CheckResult::Unknown(_) => None,
    }
}

/// Replays a `sat` model against the assertions through the ground evaluator.
fn model_replays(arena: &TermArena, assertions: &[TermId], result: &CheckResult) {
    if let CheckResult::Sat(model) = result {
        let mut assignment = Assignment::new();
        for (symbol, value) in model.iter() {
            assignment.set(symbol, value);
        }
        for (func, interp) in model.functions() {
            assignment.set_function(func, interp.clone());
        }
        for &a in assertions {
            assert_eq!(
                eval(arena, a, &assignment),
                Ok(Value::Bool(true)),
                "sat model must replay every assertion to true"
            );
        }
    }
}

#[test]
fn boolean_combination_zero_timeout_is_timeout_unknown() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Real], Sort::Real)
        .expect("declare f");
    let x = rvar(&mut arena, "x");
    let y = rvar(&mut arena, "y");
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let eq = arena.eq(fx, fy).unwrap();
    let lt = arena.real_lt(x, y).unwrap();
    let assertion = arena.or(eq, lt).unwrap();

    let config = SolverConfig::default().with_timeout(Duration::ZERO);
    let result = check_qf_uflra_online(&mut arena, &[assertion], &config).unwrap();
    assert!(
        matches!(&result, CheckResult::Unknown(reason) if reason.kind == UnknownKind::Timeout),
        "expected timeout unknown, got {result:?}"
    );
}

#[test]
fn interface_equality_forces_euf_contradiction_unsat() {
    // f(x) != f(y)  AND  x <= y  AND  y <= x.
    // LRA forces x = y; EUF then needs f(x) = f(y) by congruence, contradicting the
    // asserted f(x) != f(y) ⇒ UNSAT. The interface equality (x, y) is load-bearing.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Real], Sort::Real)
        .expect("declare f");
    let x = rvar(&mut arena, "x");
    let y = rvar(&mut arena, "y");
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let fx_ne_fy = {
        let eq = arena.eq(fx, fy).unwrap();
        arena.not(eq).unwrap()
    };
    let x_le_y = arena.real_le(x, y).unwrap();
    let y_le_x = arena.real_le(y, x).unwrap();
    let assertions = [fx_ne_fy, x_le_y, y_le_x];

    let config = SolverConfig::default();
    let online = check_qf_uflra_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(online, CheckResult::Unsat, "combination must refute");

    // Agree with the trusted offline decider.
    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(false));
}

#[test]
fn interface_equality_sat_companion() {
    // f(x) != f(y)  AND  x <= y. Here x can be strictly below y, so f(x), f(y) may
    // differ ⇒ SAT. The combination must build a real f-interpretation that replays.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Real], Sort::Real)
        .expect("declare f");
    let x = rvar(&mut arena, "x");
    let y = rvar(&mut arena, "y");
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let fx_ne_fy = {
        let eq = arena.eq(fx, fy).unwrap();
        arena.not(eq).unwrap()
    };
    let x_le_y = arena.real_le(x, y).unwrap();
    let assertions = [fx_ne_fy, x_le_y];

    let config = SolverConfig::default();
    let online = check_qf_uflra_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&online), Some(true), "expected SAT, got {online:?}");
    model_replays(&arena, &assertions, &online);

    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(true));
}

/// A free Bool symbol living *only* in the propositional skeleton (never as a theory
/// atom) must land in the returned `sat` model with the skeleton's committed truth
/// value — otherwise the witness fails to replay against the original assertions. Here
/// `¬(x < 0)` forces the disjunct `b` true, so a model that omits `b` does not satisfy
/// `(b ∨ x < 0)`.
#[test]
fn skeleton_only_bool_symbol_is_injected_into_sat_model() {
    let mut arena = TermArena::new();
    let x = rvar(&mut arena, "x");
    let zero = rconst(&mut arena, 0);
    let b_sym = arena.declare("b", Sort::Bool).expect("declare bool");
    let b = arena.var(b_sym);
    let x_lt_0 = arena.real_lt(x, zero).unwrap();
    let disj = arena.or(b, x_lt_0).unwrap();
    let neq = arena.not(x_lt_0).unwrap();
    let assertions = [disj, neq];

    let config = SolverConfig::default();
    let online = check_qf_uflra_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(
        verdict(&online),
        Some(true),
        "instance is SAT with b = true"
    );
    // The model must carry `b`, so replay evaluates `(b ∨ x < 0)` to `true`.
    let CheckResult::Sat(model) = &online else {
        panic!("expected a sat model, got {online:?}");
    };
    let mut assignment = Assignment::new();
    for (symbol, value) in model.iter() {
        assignment.set(symbol, value);
    }
    for (func, interp) in model.functions() {
        assignment.set_function(func, interp.clone());
    }
    for &a in &assertions {
        assert_eq!(
            eval(&arena, a, &assignment),
            Ok(Value::Bool(true)),
            "sat model must replay every assertion to true"
        );
    }
}

#[test]
fn pure_lra_decides() {
    // (x < y) AND (y < x): pure LRA, no UF ⇒ UNSAT.
    let mut arena = TermArena::new();
    let x = rvar(&mut arena, "x");
    let y = rvar(&mut arena, "y");
    let xy = arena.real_lt(x, y).unwrap();
    let yx = arena.real_lt(y, x).unwrap();
    let config = SolverConfig::default();
    let result = check_qf_uflra_online(&mut arena, &[xy, yx], &config).unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn pure_lra_sat_replays() {
    // x <= y AND x >= 0: pure LRA, satisfiable.
    let mut arena = TermArena::new();
    let x = rvar(&mut arena, "x");
    let y = rvar(&mut arena, "y");
    let zero = rconst(&mut arena, 0);
    let x_le_y = arena.real_le(x, y).unwrap();
    let x_ge_0 = arena.real_ge(x, zero).unwrap();
    let assertions = [x_le_y, x_ge_0];
    let config = SolverConfig::default();
    let result = check_qf_uflra_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&result), Some(true));
    model_replays(&arena, &assertions, &result);
}

#[test]
fn pure_euf_decides() {
    // f(a) = b AND f(a) != b (degenerate EUF): UNSAT, no LRA atoms.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Real], Sort::Real)
        .expect("declare f");
    let a = rvar(&mut arena, "a");
    let b = rvar(&mut arena, "b");
    let fa = arena.apply(f, &[a]).unwrap();
    let eq = arena.eq(fa, b).unwrap();
    let ne = {
        let e = arena.eq(fa, b).unwrap();
        arena.not(e).unwrap()
    };
    let config = SolverConfig::default();
    let result = check_qf_uflra_online(&mut arena, &[eq, ne], &config).unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn nested_congruence_unsat() {
    // f(f(a)) != f(f(b)) AND a <= b AND b <= a. a=b ⇒ f(a)=f(b) ⇒ f(f(a))=f(f(b)).
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Real], Sort::Real)
        .expect("declare f");
    let a = rvar(&mut arena, "a");
    let b = rvar(&mut arena, "b");
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let ffa = arena.apply(f, &[fa]).unwrap();
    let ffb = arena.apply(f, &[fb]).unwrap();
    let ne = {
        let e = arena.eq(ffa, ffb).unwrap();
        arena.not(e).unwrap()
    };
    let a_le_b = arena.real_le(a, b).unwrap();
    let b_le_a = arena.real_le(b, a).unwrap();
    let assertions = [ne, a_le_b, b_le_a];
    let config = SolverConfig::default();
    let online = check_qf_uflra_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(online, CheckResult::Unsat);

    // The offline eager-Ackermann decider may *decline* (Unknown) on a real-sorted
    // nested-UF case; when it does decide, it must agree (never SAT).
    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_ne!(verdict(&offline), Some(true), "offline must not claim SAT");
}

#[test]
fn non_uflra_atom_declines_gracefully() {
    // A bit-vector equality atom is outside QF_UFLRA ⇒ graceful Unknown, never panic.
    let mut arena = TermArena::new();
    let bv = arena.declare("v", Sort::BitVec(8)).unwrap();
    let v = arena.var(bv);
    let k = arena.bv_const(8, 5).unwrap();
    let eq = arena.eq(v, k).unwrap();
    let config = SolverConfig::default();
    let result = check_qf_uflra_online(&mut arena, &[eq], &config).unwrap();
    assert!(
        matches!(result, CheckResult::Unknown(_)),
        "expected a graceful Unknown, got {result:?}"
    );
}

#[test]
#[allow(clippy::similar_names)]
fn disjunctive_sat_replays() {
    // (x <= 0 OR f(x) = f(1)) AND x >= 1 AND x <= 1 AND f(x) != f(1).
    // x >= 1 AND x <= 1 ⇒ x = 1, refuting x <= 0, so the disjunction forces
    // f(x) = f(1)... but f(x) != f(1) is also asserted ⇒ UNSAT. (Constructed to
    // exercise the disjunction; see disjunctive_unsat for the verdict assertion.)
    //
    // Here is the genuine SAT companion: drop the f(x) != f(1) conjunct. Then with
    // x = 1, f(x) = f(1) holds by congruence, satisfying the disjunction ⇒ SAT.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Real], Sort::Real)
        .expect("declare f");
    let x = rvar(&mut arena, "x");
    let one = rconst(&mut arena, 1);
    let zero = rconst(&mut arena, 0);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();

    let x_le_0 = arena.real_le(x, zero).unwrap();
    let fx_eq_f1 = arena.eq(fx, f1).unwrap();
    let disjunction = arena.or(x_le_0, fx_eq_f1).unwrap();
    let x_ge_1 = arena.real_ge(x, one).unwrap();
    let x_le_1 = arena.real_le(x, one).unwrap();
    let assertions = [disjunction, x_ge_1, x_le_1];

    let config = SolverConfig::default();
    let online = check_qf_uflra_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&online), Some(true), "expected SAT, got {online:?}");
    model_replays(&arena, &assertions, &online);

    // Re-check the verdict test-side against the trusted offline decider.
    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(true));
}

#[test]
#[allow(clippy::similar_names)]
fn disjunctive_unsat() {
    // (x <= 0 OR f(x) = f(1)) AND x >= 1 AND x <= 1 AND f(x) != f(1).
    // x = 1 refutes x <= 0, forcing f(x) = f(1), contradicting f(x) != f(1) ⇒ UNSAT.
    // The old conjunctive path declined this (a disjunction in the skeleton).
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Real], Sort::Real)
        .expect("declare f");
    let x = rvar(&mut arena, "x");
    let one = rconst(&mut arena, 1);
    let zero = rconst(&mut arena, 0);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();

    let x_le_0 = arena.real_le(x, zero).unwrap();
    let fx_eq_f1 = arena.eq(fx, f1).unwrap();
    let disjunction = arena.or(x_le_0, fx_eq_f1).unwrap();
    let x_ge_1 = arena.real_ge(x, one).unwrap();
    let x_le_1 = arena.real_le(x, one).unwrap();
    let fx_ne_f1 = arena.not(fx_eq_f1).unwrap();
    let assertions = [disjunction, x_ge_1, x_le_1, fx_ne_f1];

    let config = SolverConfig::default();
    let online = check_qf_uflra_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(online, CheckResult::Unsat, "combination must refute");

    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(false));
}

#[test]
#[allow(clippy::similar_names)]
fn ite_over_uflra_sat_replays() {
    // ite(x >= 1, f(x) = f(1), x <= 0) AND x >= 1 AND x <= 1 AND nothing forbidding
    // f(x) = f(1). The guard x >= 1 holds (x = 1), selecting the then-branch
    // f(x) = f(1), which is consistent (x = 1 ⇒ f(x) = f(1) by congruence) ⇒ SAT.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Real], Sort::Real)
        .expect("declare f");
    let x = rvar(&mut arena, "x");
    let one = rconst(&mut arena, 1);
    let zero = rconst(&mut arena, 0);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();

    let guard = arena.real_ge(x, one).unwrap();
    let then_b = arena.eq(fx, f1).unwrap();
    let else_b = arena.real_le(x, zero).unwrap();
    let ite = arena.ite(guard, then_b, else_b).unwrap();
    let x_ge_1 = arena.real_ge(x, one).unwrap();
    let x_le_1 = arena.real_le(x, one).unwrap();
    let assertions = [ite, x_ge_1, x_le_1];

    let config = SolverConfig::default();
    let online = check_qf_uflra_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&online), Some(true), "expected SAT, got {online:?}");
    model_replays(&arena, &assertions, &online);

    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(true));
}

#[test]
#[allow(clippy::similar_names)]
fn ite_over_uflra_unsat() {
    // ite(x >= 1, f(x) = f(1), x <= 0) AND x >= 1 AND x <= 1 AND f(x) != f(1).
    // The guard holds, selecting f(x) = f(1); with f(x) != f(1) asserted ⇒ UNSAT.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Real], Sort::Real)
        .expect("declare f");
    let x = rvar(&mut arena, "x");
    let one = rconst(&mut arena, 1);
    let zero = rconst(&mut arena, 0);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();

    let guard = arena.real_ge(x, one).unwrap();
    let then_b = arena.eq(fx, f1).unwrap();
    let else_b = arena.real_le(x, zero).unwrap();
    let ite = arena.ite(guard, then_b, else_b).unwrap();
    let x_ge_1 = arena.real_ge(x, one).unwrap();
    let x_le_1 = arena.real_le(x, one).unwrap();
    let fx_ne_f1 = arena.not(then_b).unwrap();
    let assertions = [ite, x_ge_1, x_le_1, fx_ne_f1];

    let config = SolverConfig::default();
    let online = check_qf_uflra_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(online, CheckResult::Unsat);

    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(false));
}

/// Advances a 64-bit LCG and returns a 32-bit draw (no `rand` crate, no clock).
fn next_rand(state: &mut u64) -> u32 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    (*state >> 33) as u32
}

/// Builds one deterministic-random small `QF_UFLRA` conjunction over a few real vars
/// and a unary real function `f`: a conjunction of LRA order atoms and `f`-application
/// equalities / disequalities.
#[allow(clippy::many_single_char_names)]
fn build_case(arena: &mut TermArena, state: &mut u64) -> Vec<TermId> {
    let f = arena
        .declare_fun("f", &[Sort::Real], Sort::Real)
        .expect("declare f");
    let x = rvar(arena, "x");
    let y = rvar(arena, "y");
    let z = rvar(arena, "z");

    // A small pool of real terms: vars, a couple of small constants, and f-apps.
    let mut pool: Vec<TermId> = vec![x, y, z];
    for _ in 0..2 {
        let n = i128::from(next_rand(state) % 5);
        pool.push(rconst(arena, n));
    }
    // A few f-applications over pool members (and one nested application).
    for _ in 0..3 {
        let pick = pool[(next_rand(state) as usize) % pool.len()];
        let app = arena.apply(f, &[pick]).unwrap();
        pool.push(app);
    }

    // 2..4 atoms combined as a conjunction (this slice decides conjunctions).
    let atom_count = 2 + (next_rand(state) % 3) as usize;
    let mut atoms: Vec<TermId> = Vec::with_capacity(atom_count);
    for _ in 0..atom_count {
        let lhs = pool[(next_rand(state) as usize) % pool.len()];
        let rhs = pool[(next_rand(state) as usize) % pool.len()];
        let atom = match next_rand(state) % 5 {
            0 => arena.real_lt(lhs, rhs).unwrap(),
            1 => arena.real_le(lhs, rhs).unwrap(),
            2 => arena.eq(lhs, rhs).unwrap(),
            3 => {
                let e = arena.eq(lhs, rhs).unwrap();
                arena.not(e).unwrap()
            }
            _ => arena.real_ge(lhs, rhs).unwrap(),
        };
        atoms.push(atom);
    }
    atoms
}

#[test]
fn differential_fuzz_agrees_with_offline_ackermann() {
    // A per-case wall-clock budget: a hard random interface arrangement can otherwise
    // grind far past any reasonable time (the DFS is up to `3^pairs`). Expiry degrades a
    // case to a graceful `Unknown` (dropped from the jointly-decided comparison), never a
    // wrong verdict — the aggregate coverage asserts below still hold over the fast majority.
    let config = SolverConfig::default().with_timeout(Duration::from_secs(1));
    let mut jointly_decided = 0usize;
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;
    let mut online_decided = 0usize;

    let mut state: u64 = 0x1234_5678_9abc_def0;

    for _case in 0..600usize {
        let mut arena = TermArena::new();
        let assertions = build_case(&mut arena, &mut state);

        let online = check_qf_uflra_online(&mut arena, &assertions, &config).expect("online check");
        let offline =
            check_with_uf_arithmetic(&mut arena, &assertions, &config).expect("offline check");

        // Every online `sat` must replay against the originals — the trust anchor.
        model_replays(&arena, &assertions, &online);

        if verdict(&online).is_some() {
            online_decided += 1;
        }

        if let (Some(on), Some(off)) = (verdict(&online), verdict(&offline)) {
            assert_eq!(
                on, off,
                "online/offline DISAGREE on a jointly-decided case \
                 (online={online:?}, offline={offline:?}); assertions: {assertions:?}"
            );
            jointly_decided += 1;
            if on {
                sat_count += 1;
            } else {
                unsat_count += 1;
            }
        }
    }

    assert!(
        jointly_decided > 0,
        "expected some jointly-decided cases, got none"
    );
    assert!(
        online_decided > 0,
        "online decider should decide some cases (not all Unknown)"
    );
    assert!(sat_count > 0, "expected non-zero SAT coverage, got none");
    assert!(
        unsat_count > 0,
        "expected non-zero UNSAT coverage, got none"
    );
}

/// Builds a small deterministic-random pool of `QF_UFLRA` atoms over a few real vars
/// and a unary real `f`: order atoms and `f`-application equalities.
#[allow(clippy::many_single_char_names)]
fn build_atom_pool(arena: &mut TermArena, state: &mut u64) -> Vec<TermId> {
    let f = arena
        .declare_fun("f", &[Sort::Real], Sort::Real)
        .expect("declare f");
    let x = rvar(arena, "x");
    let y = rvar(arena, "y");
    let z = rvar(arena, "z");

    let mut terms: Vec<TermId> = vec![x, y, z];
    for _ in 0..2 {
        let n = i128::from(next_rand(state) % 4);
        terms.push(rconst(arena, n));
    }
    for _ in 0..3 {
        let pick = terms[(next_rand(state) as usize) % terms.len()];
        terms.push(arena.apply(f, &[pick]).unwrap());
    }

    let mut atoms: Vec<TermId> = Vec::new();
    for _ in 0..6 {
        let lhs = terms[(next_rand(state) as usize) % terms.len()];
        let rhs = terms[(next_rand(state) as usize) % terms.len()];
        let atom = match next_rand(state) % 4 {
            0 => arena.real_lt(lhs, rhs).unwrap(),
            1 => arena.real_le(lhs, rhs).unwrap(),
            2 => arena.real_ge(lhs, rhs).unwrap(),
            _ => arena.eq(lhs, rhs).unwrap(),
        };
        atoms.push(atom);
    }
    atoms
}

/// Builds a random `and`/`or`/`not` tree (depth-bounded) over the atom pool.
fn build_bool_tree(arena: &mut TermArena, pool: &[TermId], state: &mut u64, depth: u32) -> TermId {
    if depth == 0 || next_rand(state).is_multiple_of(3) {
        return pool[(next_rand(state) as usize) % pool.len()];
    }
    match next_rand(state) % 3 {
        0 => {
            let inner = build_bool_tree(arena, pool, state, depth - 1);
            arena.not(inner).unwrap()
        }
        1 => {
            let a = build_bool_tree(arena, pool, state, depth - 1);
            let b = build_bool_tree(arena, pool, state, depth - 1);
            arena.and(a, b).unwrap()
        }
        _ => {
            let a = build_bool_tree(arena, pool, state, depth - 1);
            let b = build_bool_tree(arena, pool, state, depth - 1);
            arena.or(a, b).unwrap()
        }
    }
}

#[test]
fn boolean_structured_differential_fuzz_agrees_with_offline_ackermann() {
    // The load-bearing gate for the Boolean (DPLL(T)) layer: random and/or/not trees
    // over a pool of UFLRA atoms must AGREE with the trusted offline decider on every
    // jointly-decided instance, every sat model replayed, zero disagreements.
    // Per-case wall-clock budget (see `differential_fuzz_agrees_with_offline_ackermann`):
    // a hard arrangement degrades to `Unknown`, never a wrong verdict.
    let config = SolverConfig::default().with_timeout(Duration::from_secs(1));
    let mut jointly_decided = 0usize;
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;
    let mut online_decided = 0usize;

    let mut state: u64 = 0x0bad_f00d_dead_beef;

    for _case in 0..600usize {
        let mut arena = TermArena::new();
        let pool = build_atom_pool(&mut arena, &mut state);
        // 2..3 top-level Boolean assertions over the pool.
        let assertion_count = 2 + (next_rand(&mut state) % 2) as usize;
        let assertions: Vec<TermId> = (0..assertion_count)
            .map(|_| build_bool_tree(&mut arena, &pool, &mut state, 3))
            .collect();

        let online = check_qf_uflra_online(&mut arena, &assertions, &config).expect("online check");
        let offline =
            check_with_uf_arithmetic(&mut arena, &assertions, &config).expect("offline check");

        // Every online `sat` must replay against the originals — the trust anchor.
        model_replays(&arena, &assertions, &online);

        if verdict(&online).is_some() {
            online_decided += 1;
        }

        if let (Some(on), Some(off)) = (verdict(&online), verdict(&offline)) {
            assert_eq!(
                on, off,
                "online/offline DISAGREE on a jointly-decided boolean-structured case \
                 (online={online:?}, offline={offline:?}); assertions: {assertions:?}"
            );
            jointly_decided += 1;
            if on {
                sat_count += 1;
            } else {
                unsat_count += 1;
            }
        }
    }

    assert!(
        jointly_decided > 0,
        "expected some jointly-decided boolean-structured cases, got none"
    );
    assert!(
        online_decided > 0,
        "online decider should decide some boolean-structured cases (not all Unknown)"
    );
    assert!(
        sat_count > 0,
        "expected non-zero SAT coverage on boolean-structured cases, got none"
    );
    assert!(
        unsat_count > 0,
        "expected non-zero UNSAT coverage on boolean-structured cases, got none"
    );
}

/// Builds a Boolean-structured UNSAT `QF_UFLRA` query whose *early* (low-index) theory
/// atoms already conflict, while many independent downstream atoms remain free —
/// exactly the shape early partial-assignment pruning is meant to short-circuit.
///
/// Atoms 0 and 1 are `x < y` and `y < x` (jointly LRA-UNSAT), each unit-asserted so
/// `BCP` fixes them before any decision. Then `n_free` independent disjunctions
/// `(or (u_k < v_k) (v_k < u_k))` over fresh variables force a branching factor that,
/// WITHOUT pruning, explodes the number of total propositional models enumerated
/// before the conflict on atoms {0,1} is finally seen at a leaf. WITH pruning the
/// conflict is caught on the 2-atom partial assignment and the query is `UNSAT` at once.
fn build_early_conflict_query(arena: &mut TermArena, n_free: usize) -> Vec<TermId> {
    let x = rvar(arena, "x");
    let y = rvar(arena, "y");
    let x_lt_y = arena.real_lt(x, y).unwrap();
    let y_lt_x = arena.real_lt(y, x).unwrap();
    let mut assertions = vec![x_lt_y, y_lt_x];
    for k in 0..n_free {
        let u = rvar(arena, &format!("u{k}"));
        let v = rvar(arena, &format!("v{k}"));
        let u_lt_v = arena.real_lt(u, v).unwrap();
        let v_lt_u = arena.real_lt(v, u).unwrap();
        assertions.push(arena.or(u_lt_v, v_lt_u).unwrap());
    }
    assertions
}

#[test]
fn early_theory_prune_fires_and_reduces_enumeration() {
    // Prove early theory-conflict detection (i) engages and (ii) strictly reduces the
    // number of total propositional models enumerated — without changing the verdict.
    let config = SolverConfig::default();
    let mut arena = TermArena::new();
    let assertions = build_early_conflict_query(&mut arena, 8);

    // Public path (pruning on by default) must agree with the offline decider: UNSAT.
    let online = check_qf_uflra_online(&mut arena, &assertions, &config).expect("online check");
    assert_eq!(
        verdict(&online),
        Some(false),
        "early-conflict query is UNSAT"
    );
    // The offline eager-Ackermann reference is budgeted here: its `check_auto` reduced
    // solve grinds unbounded on this disjunctive pure-LRA shape (a pre-existing check_auto
    // perf limit, not a soundness issue). Under a per-case timeout it degrades to a
    // graceful `Unknown`; when it DOES decide it must still agree with the online UNSAT.
    let offline_config = SolverConfig::default().with_timeout(Duration::from_secs(1));
    let offline =
        check_with_uf_arithmetic(&mut arena, &assertions, &offline_config).expect("offline check");
    if let Some(off) = verdict(&offline) {
        assert!(
            !off,
            "online/offline must agree on the early-conflict query (both UNSAT)"
        );
    }

    // Verdict invariant across the pruning toggle, plus the metric contrast.
    let (with_prune, prunes_fired, models_with) =
        check_qf_uflra_boolean_with_metrics(&mut arena, &assertions, &config, true);
    let (without_prune, prunes_off, models_without) =
        check_qf_uflra_boolean_with_metrics(&mut arena, &assertions, &config, false);

    assert_eq!(verdict(&with_prune), Some(false), "pruned run is UNSAT");
    assert_eq!(
        verdict(&without_prune),
        Some(false),
        "baseline run is UNSAT"
    );
    assert_eq!(prunes_off, 0, "pruning disabled must fire zero prunes");
    assert!(
        prunes_fired > 0,
        "early pruning must engage (prunes_fired > 0), got {prunes_fired}"
    );
    assert!(
        models_with < models_without,
        "pruning must reduce enumerated total models: with={models_with} \
         (prunes_fired={prunes_fired}) vs baseline={models_without}"
    );
}

/// **Slice-1 parallel-run equivalence gate (load-bearing).** The warm equality-sharing
/// `CombinedTheory` oracle must return the **identical** verdict (Sat / Unsat / Unknown)
/// to the trusted cold from-scratch `decide_conjunction` on every conjunctive instance —
/// zero disagreements. A divergence is exactly the bug slice 1 must not introduce: the
/// warm path only changes the theory solver's lifetime, never the decision. Driven over
/// both fuzz corpora's conjunctions (the `build_case` conjunctions and any `build_bool_tree`
/// assertion that happens to flatten to a conjunction of theory atoms).
#[test]
fn combined_theory_matches_cold_decide_conjunction() {
    let mut compared = 0usize;

    // Corpus A: the `build_case` conjunctions (the conjunctive fast-path's own corpus).
    let mut state: u64 = 0x1234_5678_9abc_def0;
    for _case in 0..600usize {
        let mut arena = TermArena::new();
        let assertions = build_case(&mut arena, &mut state);
        if let Some((cold, warm)) =
            axeyum_solver::combined_vs_cold_conjunction(&mut arena, &assertions)
        {
            assert_eq!(
                cold, warm,
                "warm CombinedTheory DIVERGES from cold decide_conjunction \
                 (cold={cold}, warm={warm}); assertions: {assertions:?}"
            );
            compared += 1;
        }
    }

    // Corpus B: the Boolean-tree corpus — many of its assertions flatten to a conjunction
    // of theory atoms, exercising the warm oracle on a different atom distribution.
    let mut state: u64 = 0x0bad_f00d_dead_beef;
    for _case in 0..600usize {
        let mut arena = TermArena::new();
        let pool = build_atom_pool(&mut arena, &mut state);
        let assertion_count = 2 + (next_rand(&mut state) % 2) as usize;
        let assertions: Vec<TermId> = (0..assertion_count)
            .map(|_| build_bool_tree(&mut arena, &pool, &mut state, 3))
            .collect();
        if let Some((cold, warm)) =
            axeyum_solver::combined_vs_cold_conjunction(&mut arena, &assertions)
        {
            assert_eq!(
                cold, warm,
                "warm CombinedTheory DIVERGES from cold decide_conjunction on a \
                 boolean-corpus conjunction (cold={cold}, warm={warm}); assertions: {assertions:?}"
            );
            compared += 1;
        }
    }

    assert!(
        compared > 0,
        "the parallel-run equivalence gate compared no conjunctive instances"
    );
}

/// `Some(true)`/`Some(false)` for the offline decider's sat/unsat verdict on a
/// conjunction, `None` on Unknown — the trusted reference for the slice-2 entailment
/// check.
fn offline_verdict(arena: &mut TermArena, assertions: &[TermId]) -> Option<bool> {
    // A per-case budget: the eager-Ackermann offline reference can grind unbounded on a
    // hard random conjunction (its reduced solve is budget-blind with `None`), so it must
    // carry a timeout here just like the differential fuzzes. Expiry → `None` (Unknown),
    // which the callers already treat as "skip this soundness check" — never a wrong verdict.
    let config = SolverConfig::default().with_timeout(Duration::from_secs(1));
    verdict(&check_with_uf_arithmetic(arena, assertions, &config).expect("offline check"))
}

/// The witness term refuting a propagated literal `(atom, value)`: `not(atom)` when the
/// literal is entailed true (so `asserted ∧ ¬atom` must be UNSAT), `atom` itself when
/// entailed false.
fn refuting_witness(arena: &mut TermArena, atom: TermId, value: bool) -> TermId {
    if value {
        arena.not(atom).expect("negate atom")
    } else {
        atom
    }
}

/// **Slice-2 propagation soundness + fires gate (load-bearing).** Each literal the warm
/// `CombinedTheory::propagate` reports must be GENUINELY entailed by the asserted state
/// — `asserted ∧ ¬entailed` is offline-UNSAT (a fabricated propagation would make it
/// SAT: a hard fail) — and its reason must be asserted-only. A counter proves
/// propagation FIRES (engages), so the slice is exercised, not merely falling through.
/// Mirrors `lra_online`'s `theory_propagation_is_sound_and_fires`, over the combination.
#[test]
fn combined_theory_propagation_is_sound_and_fires() {
    let mut state: u64 = 0xa5a5_1234_dead_c0de;
    let mut fired = 0usize;
    let mut confirmed = 0usize;

    for _ in 0..1500usize {
        let mut arena = TermArena::new();
        let pool = build_atom_pool(&mut arena, &mut state);

        // Assert a random subset of the pool, all true (the combination's conjunction).
        let mut asserted: Vec<(TermId, bool)> = Vec::new();
        for &atom in &pool {
            if next_rand(&mut state).is_multiple_of(2) {
                asserted.push((atom, true));
            }
        }
        if asserted.is_empty() {
            continue;
        }

        // Skip a conjunction that is itself UNSAT — propagation on a conflicted state is
        // vacuous, and every literal is then "entailed", which is not the soundness we test.
        let asserted_terms: Vec<TermId> = asserted.iter().map(|&(t, _)| t).collect();
        if offline_verdict(&mut arena, &asserted_terms) == Some(false) {
            continue;
        }

        let Some(props) = combined_theory_propagations(&mut arena, &pool, &asserted) else {
            continue;
        };

        for (atom, value, reason) in props {
            fired += 1;

            // (1) Genuine entailment: asserted ∧ ¬entailed must be offline-UNSAT.
            let witness = refuting_witness(&mut arena, atom, value);
            let mut full = asserted_terms.clone();
            full.push(witness);
            if let Some(sat) = offline_verdict(&mut arena, &full) {
                assert!(
                    !sat,
                    "UNSOUND COMBINED PROPAGATION: asserted ∧ ¬entailed is SAT \
                     (atom={atom:?}, value={value}); asserted: {asserted_terms:?}"
                );
                confirmed += 1;
            }

            // (2) Asserted-only reason: every reason literal is an asserted atom at its
            //     asserted polarity (all true here).
            for (r_atom, r_value) in &reason {
                assert!(
                    *r_value,
                    "reason literal must be asserted-true here (got false), atom {r_atom:?}"
                );
                assert!(
                    asserted.contains(&(*r_atom, true)),
                    "reason names a NON-asserted atom {r_atom:?} — unsound explanation"
                );
            }
        }
    }

    eprintln!(
        "combined-theory-propagation gate: fired={fired} propagations, \
         {confirmed} entailments offline-confirmed, 0 unsound"
    );
    assert!(
        fired > 20,
        "combined theory propagation never meaningfully fired ({fired}) — slice 2 not exercised"
    );
    assert!(
        confirmed > 10,
        "too few combined propagations offline-confirmed ({confirmed})"
    );
}

/// **Slice-2 propagation fires through the integrated `BoolSearch` path.** A
/// Boolean-structured query whose early atoms force a downstream theory entailment must
/// see combined theory propagation engage in the joint fixpoint (`props_fired > 0`),
/// confirming the wiring into `BoolSearch::solve` is live — not just the standalone
/// `propagate`. The verdict must still agree with the offline decider (verdict-invariant).
#[test]
fn combined_theory_propagation_fires_in_boolean_search() {
    // Per-case budget for the offline reference (grinds unbounded with `None`); expiry →
    // Unknown, dropped from the jointly-decided comparison, never a wrong verdict.
    let config = SolverConfig::default().with_timeout(Duration::from_secs(1));
    let mut state: u64 = 0x1357_9bdf_2468_ace0;
    let mut total_props = 0usize;
    let mut decided = 0usize;

    for _ in 0..400usize {
        let mut arena = TermArena::new();
        let pool = build_atom_pool(&mut arena, &mut state);
        let assertion_count = 2 + (next_rand(&mut state) % 2) as usize;
        let assertions: Vec<TermId> = (0..assertion_count)
            .map(|_| build_bool_tree(&mut arena, &pool, &mut state, 3))
            .collect();

        let (result, props_fired) =
            check_qf_uflra_boolean_prop_metrics(&mut arena, &assertions, &config);
        total_props += props_fired;

        // Verdict-invariant: still agrees with the offline decider on jointly-decided cases.
        model_replays(&arena, &assertions, &result);
        let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).expect("offline");
        if let (Some(on), Some(off)) = (verdict(&result), verdict(&offline)) {
            assert_eq!(
                on, off,
                "theory propagation changed the verdict (online={result:?}, offline={offline:?}); \
                 assertions: {assertions:?}"
            );
            decided += 1;
        }
    }

    assert!(decided > 0, "expected some jointly-decided cases, got none");
    assert!(
        total_props > 0,
        "combined theory propagation never fired through BoolSearch ({total_props}) — \
         the slice-2 wiring is not engaging"
    );
}

/// **Slice-3b incremental-surface-vs-`check` differential (load-bearing).** The new
/// backtrackable `impl TheorySolver` surface on `CombinedIncremental` — driven exactly as
/// the slice-3c `Dpll` will (`push`, `assert` each literal to a propagation fixpoint) —
/// must AGREE with the trusted reference [`check`] on every case it decides on its own,
/// with **zero disagreements**, and never refute a genuinely-SAT conjunction:
///
/// - `Inconsistent` ⇒ `check` must NOT be SAT (`check` may decline to `Unknown` on a
///   hard case the incremental surface still refutes — that is *more* capable, not a
///   disagreement), AND the trusted **offline Ackermann** decider — a *complete*
///   reference — must NOT call it SAT (the load-bearing soundness anchor: the incremental
///   surface must never refute a satisfiable conjunction).
/// - `Consistent` (no `Undetermined` interface pair) ⇒ `check` must NOT be UNSAT — the
///   incremental surface agrees with the slice's own reference. (It is *not* asserted
///   that offline cannot be UNSAT: like `check`, the incremental surface is intentionally
///   incomplete on disequalities outside an interface pair — it does not *claim* SAT, only
///   "no conflict found", exactly as `check` returns `Unknown` on the same shape, so the
///   slice-3c `Dpll` returns `Unknown` there too, never a wrong SAT.)
/// - `Deferred` (an `Undetermined` pair only the slice-3c case-split resolves) imposes
///   no constraint — the honest handles/defers split.
///
/// A single wrong-direction verdict — incremental Inconsistent on an offline-SAT case, or
/// Consistent on a `check`-UNSAT case — is a hard failure. Driven over both fuzz corpora's
/// conjunctions, mirroring `combined_theory_matches_cold_decide_conjunction`.
#[test]
fn combined_incremental_surface_matches_check() {
    // verdict codes: 0 = Unsat, 1 = Sat, 2 = Unknown.
    let mut handled = 0usize;
    let mut deferred = 0usize;
    let mut consistent = 0usize;
    let mut inconsistent = 0usize;
    // Per-case budget for the offline soundness anchor (grinds unbounded with `None`);
    // expiry → Unknown, which every branch's `assert_ne!` already tolerates (Unknown is
    // neither `Some(true)` nor `Some(false)`), never a wrong verdict.
    let config = SolverConfig::default().with_timeout(Duration::from_secs(1));

    let mut run = |assertions: &[TermId], arena: &mut TermArena| {
        let Some((decision, check)) = combined_incremental_vs_check(arena, assertions) else {
            return;
        };
        // The trusted soundness anchor: the offline Ackermann verdict.
        let offline =
            verdict(&check_with_uf_arithmetic(arena, assertions, &config).expect("offline"));
        match decision {
            IncrementalDecision::Inconsistent => {
                assert_ne!(
                    offline,
                    Some(true),
                    "UNSOUND: incremental Inconsistent on an offline-SAT case; \
                     assertions: {assertions:?}"
                );
                assert_ne!(
                    check, 1,
                    "incremental Inconsistent but check is SAT (check={check}); \
                     assertions: {assertions:?}"
                );
                handled += 1;
                inconsistent += 1;
            }
            IncrementalDecision::Consistent => {
                assert_ne!(
                    check, 0,
                    "incremental Consistent (no undetermined pair) but check is UNSAT; \
                     assertions: {assertions:?}"
                );
                handled += 1;
                consistent += 1;
            }
            IncrementalDecision::Deferred => deferred += 1,
        }
    };

    // Corpus A: the `build_case` conjunctions.
    let mut state: u64 = 0x1234_5678_9abc_def0;
    for _case in 0..600usize {
        let mut arena = TermArena::new();
        let assertions = build_case(&mut arena, &mut state);
        run(&assertions, &mut arena);
    }

    // Corpus B: the Boolean-tree corpus's conjunctive assertions.
    let mut state: u64 = 0x0bad_f00d_dead_beef;
    for _case in 0..600usize {
        let mut arena = TermArena::new();
        let pool = build_atom_pool(&mut arena, &mut state);
        let assertion_count = 2 + (next_rand(&mut state) % 2) as usize;
        let assertions: Vec<TermId> = (0..assertion_count)
            .map(|_| build_bool_tree(&mut arena, &pool, &mut state, 3))
            .collect();
        run(&assertions, &mut arena);
    }

    eprintln!(
        "slice-3b incremental-vs-check: handled={handled} (consistent={consistent}, \
         inconsistent={inconsistent}), deferred={deferred}, 0 unsound disagreements"
    );
    assert!(
        handled > 0,
        "the incremental surface decided no case on its own — gate not exercised"
    );
    assert!(
        inconsistent > 0,
        "the incremental surface never detected a conflict — the Inconsistent path is untested"
    );
    assert!(
        consistent > 0,
        "the incremental surface never confirmed a consistent case — Consistent path untested"
    );
}

/// **Slice-3b interface-variable registration structure (slice-3c hand-off check).** The
/// `CombinedIncremental` must register its interface variables FRESH — beyond the
/// original atom count — three per shared pair (`eq` / `lt` / `gt`), all distinct, and
/// its structural clauses (`eq ∨ lt ∨ gt`, the three pairwise exclusions) must reference
/// only those registered variables. This is the surface slice 3c adds to the SAT clause
/// DB; the slice does not yet wire it in.
#[test]
fn combined_incremental_registers_fresh_interface_vars() {
    let mut state: u64 = 0xfeed_face_0000_1111;
    let mut saw_pairs = 0usize;

    for _ in 0..400usize {
        let mut arena = TermArena::new();
        let pool = build_atom_pool(&mut arena, &mut state);
        let assertion_count = 2 + (next_rand(&mut state) % 2) as usize;
        let assertions: Vec<TermId> = (0..assertion_count)
            .map(|_| build_bool_tree(&mut arena, &pool, &mut state, 3))
            .collect();

        let Some((original_count, pairs, clauses)) =
            combined_incremental_structure(&mut arena, &assertions)
        else {
            continue;
        };

        let mut all_vars = std::collections::BTreeSet::new();
        for (i, &(eq, lt, gt)) in pairs.iter().enumerate() {
            // Fresh: every interface variable is beyond the original atom numbering.
            for v in [eq, lt, gt] {
                assert!(
                    v >= original_count,
                    "interface var {v} not fresh (original_count={original_count})"
                );
                assert!(all_vars.insert(v), "interface var {v} registered twice");
            }
            // Three vars per pair, contiguous in registration order.
            assert_eq!(eq, original_count + i * 3);
            assert_eq!(lt, original_count + i * 3 + 1);
            assert_eq!(gt, original_count + i * 3 + 2);
        }

        // Exactly four structural clauses per pair, over registered variables only.
        assert_eq!(clauses.len(), pairs.len() * 4);
        for clause in &clauses {
            for &(v, _) in clause {
                assert!(
                    all_vars.contains(&v),
                    "structural clause references unregistered var {v}"
                );
            }
        }
        if !pairs.is_empty() {
            saw_pairs += 1;
        }
    }

    assert!(
        saw_pairs > 0,
        "no instance registered an interface pair — the registration path is untested"
    );
}
