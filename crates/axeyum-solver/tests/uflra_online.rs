//! Integration tests for the online (model-based) `Nelson–Oppen` combination of
//! `EUF` + linear real arithmetic — `check_qf_uflra_online`.
//!
//! The load-bearing test is the **differential fuzz** against the trusted offline
//! decider `check_with_uf_arithmetic` (eager Ackermann): over many deterministic
//! random `QF_UFLRA` conjunctions the online combination must AGREE (sat / unsat)
//! with the offline decider on every jointly-decided instance — zero disagreements —
//! and every `sat` model must replay against the original assertions. A graceful
//! `Unknown` on a hard case is fine; a wrong sat / unsat is unacceptable.

use axeyum_ir::{Assignment, Rational, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, check_qf_uflra_online, check_with_uf_arithmetic};

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
    let config = SolverConfig::default();
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
    if depth == 0 || next_rand(state) % 3 == 0 {
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
    let config = SolverConfig::default();
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
