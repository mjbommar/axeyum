//! Never-crash / never-unsound corpus for adversarial large-magnitude rational
//! constants.
//!
//! The cardinal rule: the public `solve()` must never panic and never produce a
//! wrong `Sat`/`Unsat` on a query whose arithmetic leaves the `i128` fast path.
//! This corpus drives the public entry points on such queries and asserts a
//! sound outcome (`Ok(_)`, never a panic, never a wrong verdict).
//!
//! **Since ADR-1702 the expected outcome is no longer "`Unknown`, full stop".**
//! Exact rationals now PROMOTE to arbitrary precision instead of overflowing, so
//! a query that used to degrade may now be decided correctly. Each test here
//! therefore asserts against the verdict that would be *wrong* for its query,
//! never against the correct one — asserting "not `Sat`" on a satisfiable query
//! is a test that forbids the right answer.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Rational, TermArena};
use axeyum_solver::{CheckResult, SolverConfig, solve};

/// The original repro: `x = i128::MAX ∧ x*x > i128::MAX` over the reals drove a
/// `Rational::mul` overflow panic through the NRA → LRA scale path. It must
/// return `Ok(_)` and never panic.
///
/// **This test's assertion changed with ADR-1702.** It used to forbid `Sat`, on
/// the ground that "the verdict cannot be soundly computed from overflowed
/// values". Exact rational arithmetic no longer overflows — it promotes to
/// arbitrary precision — so `x·x` for `x = i128::MAX` is now an exact value and
/// the query is plainly **satisfiable**. Forbidding `Sat` would forbid the
/// correct answer. The wrong verdict here is `Unsat`, and that is what is
/// asserted against; a graceful `Unknown` also remains acceptable.
#[test]
fn huge_rational_real_mul_is_graceful_not_crash() {
    let mut a = TermArena::new();
    let x = a.real_var("x").unwrap();
    let huge = a.real_const(Rational::integer(i128::MAX));
    let x_eq_huge = a.eq(x, huge).unwrap();
    let xx = a.real_mul(x, x).unwrap();
    let huge2 = a.real_const(Rational::integer(i128::MAX));
    let xx_gt = a.real_gt(xx, huge2).unwrap();

    let result =
        solve(&mut a, &[x_eq_huge, xx_gt], &SolverConfig::default()).expect("solve must not error");
    // `x = i128::MAX` satisfies `x·x > i128::MAX`, so the only wrong verdict is
    // `Unsat`.
    assert!(
        !matches!(result, CheckResult::Unsat),
        "satisfiable huge-product real query must not be reported Unsat; got {result:?}"
    );
}

/// A purely LINEAR real query whose coefficients are `i128::MAX`: scaling and
/// cross-multiplication in Fourier–Motzkin / simplex can overflow. The result
/// must be `Ok(_)`, no panic, and not a wrong verdict. `i128::MAX·x = i128::MAX`
/// is satisfiable (x = 1), but if the engine overflows it must degrade to
/// `Unknown` rather than answer `Unsat`.
#[test]
fn huge_rational_linear_is_graceful() {
    let mut a = TermArena::new();
    let x = a.real_var("x").unwrap();
    let big = a.real_const(Rational::new(i128::MAX, 1));
    let big_x = a.real_mul(big, x).unwrap();
    let big_rhs = a.real_const(Rational::new(i128::MAX, 1));
    // i128::MAX·x = i128::MAX  (x = 1 satisfies it).
    let eq = a.eq(big_x, big_rhs).unwrap();

    let result = solve(&mut a, &[eq], &SolverConfig::default()).expect("solve must not error");
    // It is satisfiable, so the only wrong verdict is `Unsat`.
    assert!(
        !matches!(result, CheckResult::Unsat),
        "satisfiable huge-coefficient linear query must not be Unsat; got {result:?}"
    );
}

/// `bv2nat` of a 128-bit var constrained `>= i128::MAX`: the finite-range
/// abstraction must not panic. Either a sound verdict or a graceful `Unknown` is
/// acceptable; a wrong verdict is not. (`bv2nat` of 128 bits ranges over
/// `[0, 2^128 - 1]`, which exceeds `i128`, so the engine currently declines to
/// `Unknown` — assert it does not crash and is not unsound.)
#[test]
fn bv2nat_width_128_is_graceful() {
    let mut a = TermArena::new();
    let b = a.bv_var("b", 128).unwrap();
    let n = a.bv2nat(b).unwrap();
    let huge = a.int_const(i128::MAX);
    let ge = a.int_ge(n, huge).unwrap();

    let result = solve(&mut a, &[ge], &SolverConfig::default()).expect("solve must not error");
    // `bv2nat(128-bit) >= i128::MAX` is satisfiable over the 128-bit range, so the
    // only wrong verdict is `Unsat`. (A graceful `Unknown` is the expected answer.)
    assert!(
        !matches!(result, CheckResult::Unsat),
        "bv2nat width-128 bound must not be a wrong Unsat; got {result:?}"
    );
}

/// Proving `unsat` under a 1-nanosecond timeout must fail CLOSED: an unsat 8-bit
/// query (`b = 0 ∧ b = 1`) asked to prove its `unsat` with an essentially-zero
/// budget must return `Ok(Unknown(_))` — never `Unsat` without a checked proof,
/// and never a crash.
#[test]
fn prove_unsat_under_tiny_timeout_is_unknown_not_crash() {
    let mut a = TermArena::new();
    let b = a.bv_var("b", 8).unwrap();
    let zero = a.bv_const(8, 0).unwrap();
    let one = a.bv_const(8, 1).unwrap();
    let b_is_zero = a.eq(b, zero).unwrap();
    let b_is_one = a.eq(b, one).unwrap();

    let config = SolverConfig::default()
        .with_prove_unsat(true)
        .with_timeout(Duration::from_nanos(1));
    let result = solve(&mut a, &[b_is_zero, b_is_one], &config).expect("solve must not error");
    assert!(
        matches!(result, CheckResult::Unknown(_)),
        "prove-unsat under a 1ns budget must fail closed to Unknown; got {result:?}"
    );
}

/// Solving the same query twice on the same arena must yield identical verdicts —
/// the solver must not carry stale state across calls. (A real query, not a
/// pathological one: `x = 3 ∧ x > 0`, satisfiable both times.)
#[test]
fn repeated_solve_same_arena_is_consistent() {
    let mut a = TermArena::new();
    let x = a.real_var("x").unwrap();
    let three = a.real_const(Rational::integer(3));
    let x_eq_3 = a.eq(x, three).unwrap();
    let zero = a.real_const(Rational::zero());
    let x_gt_0 = a.real_gt(x, zero).unwrap();
    let assertions = [x_eq_3, x_gt_0];

    let first = solve(&mut a, &assertions, &SolverConfig::default()).expect("solve must not error");
    let second =
        solve(&mut a, &assertions, &SolverConfig::default()).expect("solve must not error");

    // Same verdict class both times (freshness; no stale state). Compare the
    // discriminant, not the model (a Sat model object differs by construction).
    let class = |r: &CheckResult| match r {
        CheckResult::Sat(_) => 0,
        CheckResult::Unsat => 1,
        CheckResult::Unknown(_) => 2,
    };
    assert_eq!(
        class(&first),
        class(&second),
        "repeated solve on the same arena changed verdict: {first:?} then {second:?}"
    );
}
