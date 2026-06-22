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
use axeyum_solver::{CheckResult, SolverConfig, check_qf_uflia_online, check_with_uf_arithmetic};

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
