//! Integration tests for the online (model-based) `Nelson–Oppen` combination of
//! `EUF` + linear integer arithmetic — `check_qf_uflia_online`.
//!
//! The load-bearing test is the **differential fuzz** against the trusted offline
//! decider `check_with_uf_arithmetic` (eager Ackermann): over many deterministic
//! random `QF_UFLIA` conjunctions the online combination must AGREE (sat / unsat)
//! with the offline decider on every jointly-decided instance — zero disagreements —
//! and every `sat` model must replay against the original assertions with **integer**
//! values. A graceful `Unknown` on a hard case is fine; a wrong sat / unsat is
//! unacceptable.

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, SolverConfig, check_qf_uflia_boolean_with_metrics, check_qf_uflia_online,
    check_with_uf_arithmetic,
};

fn iconst(arena: &mut TermArena, n: i128) -> TermId {
    arena.int_const(n)
}

fn ivar(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, Sort::Int).expect("declare int");
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

/// Replays a `sat` model against the assertions through the ground evaluator, checking
/// every model symbol value is an integer.
fn model_replays(arena: &TermArena, assertions: &[TermId], result: &CheckResult) {
    if let CheckResult::Sat(model) = result {
        let mut assignment = Assignment::new();
        for (symbol, value) in model.iter() {
            assert!(
                matches!(value, Value::Int(_)),
                "sat model symbol value must be an integer, got {value:?}"
            );
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
    // LIA forces x = y; EUF then needs f(x) = f(y) by congruence, contradicting the
    // asserted f(x) != f(y) ⇒ UNSAT. The interface equality (x, y) is load-bearing.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let y = ivar(&mut arena, "y");
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let fx_ne_fy = {
        let eq = arena.eq(fx, fy).unwrap();
        arena.not(eq).unwrap()
    };
    let x_le_y = arena.int_le(x, y).unwrap();
    let y_le_x = arena.int_le(y, x).unwrap();
    let assertions = [fx_ne_fy, x_le_y, y_le_x];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(online, CheckResult::Unsat, "combination must refute");

    // Agree with the trusted offline decider.
    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(false));
}

#[test]
fn interface_equality_sat_companion() {
    // f(x) != f(y)  AND  x <= y. Here x can be strictly below y, so f(x), f(y) may
    // differ ⇒ SAT. The combination must build an integer f-interpretation that replays.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let y = ivar(&mut arena, "y");
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let fx_ne_fy = {
        let eq = arena.eq(fx, fy).unwrap();
        arena.not(eq).unwrap()
    };
    let x_le_y = arena.int_le(x, y).unwrap();
    let assertions = [fx_ne_fy, x_le_y];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&online), Some(true), "expected SAT, got {online:?}");
    model_replays(&arena, &assertions, &online);

    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(true));
}

#[test]
fn integer_tightening_interface_unsat() {
    // 0 < x  AND  x < 2  AND  f(x) != f(1).
    // Over ℤ, 0 < x < 2 forces x = 1, so the interface equality x = 1 holds, hence
    // f(x) = f(1) by congruence, contradicting f(x) != f(1) ⇒ UNSAT. This bites only
    // because LIA is *integer*-tight (rationally x could be 0.5 and avoid the
    // equality). The shared interface term is the constant 1.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let zero = iconst(&mut arena, 0);
    let one = iconst(&mut arena, 1);
    let two = iconst(&mut arena, 2);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();
    let fx_ne_f1 = {
        let eq = arena.eq(fx, f1).unwrap();
        arena.not(eq).unwrap()
    };
    let zero_lt_x = arena.int_lt(zero, x).unwrap();
    let x_lt_two = arena.int_lt(x, two).unwrap();
    let assertions = [zero_lt_x, x_lt_two, fx_ne_f1];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(
        online,
        CheckResult::Unsat,
        "integer tightening must force x = 1 and refute"
    );

    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(false));
}

#[test]
fn integer_tightening_interface_sat_companion() {
    // 0 < x  AND  x < 3  AND  f(x) != f(1).
    // Over ℤ, x can be 2 (≠ 1), so f(x) and f(1) may differ ⇒ SAT.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let zero = iconst(&mut arena, 0);
    let one = iconst(&mut arena, 1);
    let three = iconst(&mut arena, 3);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();
    let fx_ne_f1 = {
        let eq = arena.eq(fx, f1).unwrap();
        arena.not(eq).unwrap()
    };
    let zero_lt_x = arena.int_lt(zero, x).unwrap();
    let x_lt_three = arena.int_lt(x, three).unwrap();
    let assertions = [zero_lt_x, x_lt_three, fx_ne_f1];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&online), Some(true), "expected SAT, got {online:?}");
    model_replays(&arena, &assertions, &online);

    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(true));
}

#[test]
fn pure_lia_decides() {
    // (x < y) AND (y < x): pure LIA, no UF ⇒ UNSAT.
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let y = ivar(&mut arena, "y");
    let xy = arena.int_lt(x, y).unwrap();
    let yx = arena.int_lt(y, x).unwrap();
    let config = SolverConfig::default();
    let result = check_qf_uflia_online(&mut arena, &[xy, yx], &config).unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn pure_lia_strict_tightening_unsat() {
    // 0 < x AND x < 1: pure LIA, integer-UNSAT (rationally SAT) — the LIA point.
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let zero = iconst(&mut arena, 0);
    let one = iconst(&mut arena, 1);
    let gt = arena.int_gt(x, zero).unwrap();
    let lt = arena.int_lt(x, one).unwrap();
    let config = SolverConfig::default();
    let result = check_qf_uflia_online(&mut arena, &[gt, lt], &config).unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn pure_lia_sat_replays() {
    // x <= y AND x >= 0: pure LIA, satisfiable.
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let y = ivar(&mut arena, "y");
    let zero = iconst(&mut arena, 0);
    let x_le_y = arena.int_le(x, y).unwrap();
    let x_ge_0 = arena.int_ge(x, zero).unwrap();
    let assertions = [x_le_y, x_ge_0];
    let config = SolverConfig::default();
    let result = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&result), Some(true));
    model_replays(&arena, &assertions, &result);
}

#[test]
fn pure_euf_decides() {
    // f(a) = b AND f(a) != b (degenerate EUF): UNSAT, no LIA atoms.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let a = ivar(&mut arena, "a");
    let b = ivar(&mut arena, "b");
    let fa = arena.apply(f, &[a]).unwrap();
    let eq = arena.eq(fa, b).unwrap();
    let ne = {
        let e = arena.eq(fa, b).unwrap();
        arena.not(e).unwrap()
    };
    let config = SolverConfig::default();
    let result = check_qf_uflia_online(&mut arena, &[eq, ne], &config).unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn nested_congruence_unsat() {
    // f(f(a)) != f(f(b)) AND a <= b AND b <= a. a=b ⇒ f(a)=f(b) ⇒ f(f(a))=f(f(b)).
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let a = ivar(&mut arena, "a");
    let b = ivar(&mut arena, "b");
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let ffa = arena.apply(f, &[fa]).unwrap();
    let ffb = arena.apply(f, &[fb]).unwrap();
    let ne = {
        let e = arena.eq(ffa, ffb).unwrap();
        arena.not(e).unwrap()
    };
    let a_le_b = arena.int_le(a, b).unwrap();
    let b_le_a = arena.int_le(b, a).unwrap();
    let assertions = [ne, a_le_b, b_le_a];
    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(online, CheckResult::Unsat);

    // The offline eager-Ackermann decider may *decline* (Unknown) on a nested-UF case;
    // when it does decide, it must agree (never SAT).
    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_ne!(verdict(&offline), Some(true), "offline must not claim SAT");
}

#[test]
fn non_uflia_atom_declines_gracefully() {
    // A bit-vector equality atom is outside QF_UFLIA ⇒ graceful Unknown, never panic.
    let mut arena = TermArena::new();
    let bv = arena.declare("v", Sort::BitVec(8)).unwrap();
    let v = arena.var(bv);
    let k = arena.bv_const(8, 5).unwrap();
    let eq = arena.eq(v, k).unwrap();
    let config = SolverConfig::default();
    let result = check_qf_uflia_online(&mut arena, &[eq], &config).unwrap();
    assert!(
        matches!(result, CheckResult::Unknown(_)),
        "expected a graceful Unknown, got {result:?}"
    );
}

#[test]
#[allow(clippy::similar_names)]
fn disjunctive_sat_replays() {
    // (x <= 0 OR f(x) = f(1)) AND x >= 1 AND x <= 1.
    // x >= 1 AND x <= 1 ⇒ x = 1, refuting x <= 0, so the disjunction is satisfied by
    // f(x) = f(1), which holds by congruence (x = 1) ⇒ SAT.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let one = iconst(&mut arena, 1);
    let zero = iconst(&mut arena, 0);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();

    let x_le_0 = arena.int_le(x, zero).unwrap();
    let fx_eq_f1 = arena.eq(fx, f1).unwrap();
    let disjunction = arena.or(x_le_0, fx_eq_f1).unwrap();
    let x_ge_1 = arena.int_ge(x, one).unwrap();
    let x_le_1 = arena.int_le(x, one).unwrap();
    let assertions = [disjunction, x_ge_1, x_le_1];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
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
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let one = iconst(&mut arena, 1);
    let zero = iconst(&mut arena, 0);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();

    let x_le_0 = arena.int_le(x, zero).unwrap();
    let fx_eq_f1 = arena.eq(fx, f1).unwrap();
    let disjunction = arena.or(x_le_0, fx_eq_f1).unwrap();
    let x_ge_1 = arena.int_ge(x, one).unwrap();
    let x_le_1 = arena.int_le(x, one).unwrap();
    let fx_ne_f1 = arena.not(fx_eq_f1).unwrap();
    let assertions = [disjunction, x_ge_1, x_le_1, fx_ne_f1];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(online, CheckResult::Unsat, "combination must refute");

    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(false));
}

#[test]
#[allow(clippy::similar_names)]
fn ite_over_uflia_sat_replays() {
    // ite(x >= 1, f(x) = f(1), x <= 0) AND x >= 1 AND x <= 1 AND nothing forbidding
    // f(x) = f(1). The guard x >= 1 holds (x = 1), selecting the then-branch
    // f(x) = f(1), which is consistent (x = 1 ⇒ f(x) = f(1) by congruence) ⇒ SAT.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let one = iconst(&mut arena, 1);
    let zero = iconst(&mut arena, 0);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();

    let guard = arena.int_ge(x, one).unwrap();
    let then_b = arena.eq(fx, f1).unwrap();
    let else_b = arena.int_le(x, zero).unwrap();
    let ite = arena.ite(guard, then_b, else_b).unwrap();
    let x_ge_1 = arena.int_ge(x, one).unwrap();
    let x_le_1 = arena.int_le(x, one).unwrap();
    let assertions = [ite, x_ge_1, x_le_1];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&online), Some(true), "expected SAT, got {online:?}");
    model_replays(&arena, &assertions, &online);

    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(true));
}

#[test]
#[allow(clippy::similar_names)]
fn ite_over_uflia_unsat() {
    // ite(x >= 1, f(x) = f(1), x <= 0) AND x >= 1 AND x <= 1 AND f(x) != f(1).
    // The guard holds, selecting f(x) = f(1); with f(x) != f(1) asserted ⇒ UNSAT.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let one = iconst(&mut arena, 1);
    let zero = iconst(&mut arena, 0);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();

    let guard = arena.int_ge(x, one).unwrap();
    let then_b = arena.eq(fx, f1).unwrap();
    let else_b = arena.int_le(x, zero).unwrap();
    let ite = arena.ite(guard, then_b, else_b).unwrap();
    let x_ge_1 = arena.int_ge(x, one).unwrap();
    let x_le_1 = arena.int_le(x, one).unwrap();
    let fx_ne_f1 = arena.not(then_b).unwrap();
    let assertions = [ite, x_ge_1, x_le_1, fx_ne_f1];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
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

/// Builds one deterministic-random small `QF_UFLIA` conjunction over a few integer vars
/// and a unary integer function `f`: a conjunction of LIA order atoms and
/// `f`-application equalities / disequalities.
#[allow(clippy::many_single_char_names)]
fn build_case(arena: &mut TermArena, state: &mut u64) -> Vec<TermId> {
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(arena, "x");
    let y = ivar(arena, "y");
    let z = ivar(arena, "z");

    // A small pool of integer terms: vars, a couple of small constants, and f-apps.
    let mut pool: Vec<TermId> = vec![x, y, z];
    for _ in 0..2 {
        let n = i128::from(next_rand(state) % 5);
        pool.push(iconst(arena, n));
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
            0 => arena.int_lt(lhs, rhs).unwrap(),
            1 => arena.int_le(lhs, rhs).unwrap(),
            2 => arena.eq(lhs, rhs).unwrap(),
            3 => {
                let e = arena.eq(lhs, rhs).unwrap();
                arena.not(e).unwrap()
            }
            _ => arena.int_ge(lhs, rhs).unwrap(),
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

        let online = check_qf_uflia_online(&mut arena, &assertions, &config).expect("online check");
        let offline =
            check_with_uf_arithmetic(&mut arena, &assertions, &config).expect("offline check");

        // Every online `sat` must replay against the originals with integer values —
        // the trust anchor.
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

/// Builds a small deterministic-random pool of `QF_UFLIA` atoms over a few integer vars
/// and a unary integer `f`: order atoms and `f`-application equalities.
#[allow(clippy::many_single_char_names)]
fn build_atom_pool(arena: &mut TermArena, state: &mut u64) -> Vec<TermId> {
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(arena, "x");
    let y = ivar(arena, "y");
    let z = ivar(arena, "z");

    let mut terms: Vec<TermId> = vec![x, y, z];
    for _ in 0..2 {
        let n = i128::from(next_rand(state) % 4);
        terms.push(iconst(arena, n));
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
            0 => arena.int_lt(lhs, rhs).unwrap(),
            1 => arena.int_le(lhs, rhs).unwrap(),
            2 => arena.int_ge(lhs, rhs).unwrap(),
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
    // over a pool of UFLIA atoms must AGREE with the trusted offline decider on every
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

        let online = check_qf_uflia_online(&mut arena, &assertions, &config).expect("online check");
        let offline =
            check_with_uf_arithmetic(&mut arena, &assertions, &config).expect("offline check");

        // Every online `sat` must replay against the originals with integer values —
        // the trust anchor.
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

/// Builds a Boolean-structured UNSAT `QF_UFLIA` query whose *early* (low-index) theory
/// atoms already conflict, while many independent downstream atoms remain free —
/// exactly the shape early partial-assignment pruning is meant to short-circuit.
///
/// Atoms 0 and 1 are `x < y` and `y < x` (jointly LIA-UNSAT), each unit-asserted so
/// `BCP` fixes them before any decision. Then `n_free` independent disjunctions
/// `(or (u_k < v_k) (v_k < u_k))` over fresh variables force a branching factor that,
/// WITHOUT pruning, explodes the number of total propositional models enumerated
/// before the conflict on atoms {0,1} is finally seen at a leaf. WITH pruning the
/// conflict is caught on the 2-atom partial assignment and the query is `UNSAT` at once.
fn build_early_conflict_query(arena: &mut TermArena, n_free: usize) -> Vec<TermId> {
    let x = ivar(arena, "x");
    let y = ivar(arena, "y");
    let x_lt_y = arena.int_lt(x, y).unwrap();
    let y_lt_x = arena.int_lt(y, x).unwrap();
    let mut assertions = vec![x_lt_y, y_lt_x];
    for k in 0..n_free {
        let u = ivar(arena, &format!("u{k}"));
        let v = ivar(arena, &format!("v{k}"));
        let u_lt_v = arena.int_lt(u, v).unwrap();
        let v_lt_u = arena.int_lt(v, u).unwrap();
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
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).expect("online check");
    let offline =
        check_with_uf_arithmetic(&mut arena, &assertions, &config).expect("offline check");
    assert_eq!(
        verdict(&online),
        Some(false),
        "early-conflict query is UNSAT"
    );
    assert_eq!(
        verdict(&online),
        verdict(&offline),
        "online/offline must agree on the early-conflict query"
    );

    // Verdict invariant across the pruning toggle, plus the metric contrast.
    let (with_prune, prunes_fired, models_with) =
        check_qf_uflia_boolean_with_metrics(&mut arena, &assertions, &config, true);
    let (without_prune, prunes_off, models_without) =
        check_qf_uflia_boolean_with_metrics(&mut arena, &assertions, &config, false);

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
