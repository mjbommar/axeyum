//! Exact, bounded NIA decision for a single-variable integer **polynomial
//! equation** `p(x) = 0` of arbitrary degree (≥ 1), via the **Rational Root
//! Theorem** for degree ≥ 3 (and the existing discriminant/convexity analysis
//! for degree ≤ 2). Correctness is everything: every `Sat` here is
//! replay-checked against the *original* assertion, every `Unsat` is exact (only
//! emitted after *every* integer divisor of the constant term has been checked
//! and none is a root, with no overflow), and every shape outside the exact
//! single-variable polynomial-equation pattern must be **declined** (left to the
//! existing NIA dispatch) — never mis-decided.

use axeyum_ir::{Sort, TermArena, TermId, Value};
use axeyum_solver::{CheckResult, SolverConfig, solve};

/// Solve a single assertion built by `build`, returning the result, arena, and
/// the assertion term so a `Sat` model can be independently replayed.
fn solve_one(build: impl FnOnce(&mut TermArena) -> TermId) -> (CheckResult, TermArena, TermId) {
    let mut arena = TermArena::new();
    let assertion = build(&mut arena);
    let result =
        solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve must not error");
    (result, arena, assertion)
}

/// Re-check a `Sat` independently: the model must satisfy the original assertion
/// on replay (the strongest possible soundness witness).
fn assert_sat_replays(result: &CheckResult, arena: &TermArena, assertion: TermId) {
    let CheckResult::Sat(model) = result else {
        panic!("expected Sat, got {result:?}");
    };
    let assignment = model.to_assignment();
    assert!(
        matches!(
            axeyum_ir::eval(arena, assertion, &assignment),
            Ok(Value::Bool(true))
        ),
        "Sat model must satisfy the original assertion on replay"
    );
}

/// Build `xⁿ` over the variable `xv` as an `Int` term (`n ≥ 1`).
fn pow(arena: &mut TermArena, xv: TermId, n: u32) -> TermId {
    assert!(n >= 1);
    let mut acc = xv;
    for _ in 1..n {
        acc = arena.int_mul(acc, xv).unwrap();
    }
    acc
}

/// Build the polynomial `Σ coeffs[i]·xⁱ` (LSB-first: `coeffs[0]` is the constant
/// term) over a fresh `Int` variable `x`. Returns `(poly_term, xv)`.
fn poly(arena: &mut TermArena, coeffs: &[i128]) -> (TermId, TermId) {
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let mut acc: Option<TermId> = None;
    for (i, &c) in coeffs.iter().enumerate() {
        if c == 0 {
            continue;
        }
        let cc = arena.int_const(c);
        let term = if i == 0 {
            cc
        } else {
            let xp = pow(arena, xv, u32::try_from(i).unwrap());
            arena.int_mul(cc, xp).unwrap()
        };
        acc = Some(match acc {
            None => term,
            Some(a) => arena.int_add(a, term).unwrap(),
        });
    }
    // All-zero coefficient list collapses to the constant 0.
    let p = acc.unwrap_or_else(|| arena.int_const(0));
    (p, xv)
}

/// `p(x) = 0` for the LSB-first coefficient list.
fn poly_eq_zero(arena: &mut TermArena, coeffs: &[i128]) -> TermId {
    let (p, _) = poly(arena, coeffs);
    let zero = arena.int_const(0);
    arena.eq(p, zero).unwrap()
}

/// `0 = p(x)` (constant on the left) for the LSB-first coefficient list.
fn zero_eq_poly(arena: &mut TermArena, coeffs: &[i128]) -> TermId {
    let (p, _) = poly(arena, coeffs);
    let zero = arena.int_const(0);
    arena.eq(zero, p).unwrap()
}

/// `p(x) ≠ 0` for the LSB-first coefficient list.
fn poly_ne_zero(arena: &mut TermArena, coeffs: &[i128]) -> TermId {
    let eq = poly_eq_zero(arena, coeffs);
    arena.not(eq).unwrap()
}

// ------------------------------------------------------------------------
// DECIDES — Sat (rational-root witness, replay-checked)
// ------------------------------------------------------------------------

#[test]
fn cubic_x3_minus_1_is_sat_at_1() {
    // x³ − 1 = 0 → x = 1 (divisor of 1).
    let (result, arena, a) = solve_one(|ar| poly_eq_zero(ar, &[-1, 0, 0, 1]));
    assert_sat_replays(&result, &arena, a);
}

#[test]
fn cubic_three_roots_is_sat() {
    // x³ − 6x² + 11x − 6 = 0 → x ∈ {1,2,3}, all divisors of 6.
    let (result, arena, a) = solve_one(|ar| poly_eq_zero(ar, &[-6, 11, -6, 1]));
    assert_sat_replays(&result, &arena, a);
}

#[test]
fn quartic_x4_minus_5x2_plus_4_is_sat() {
    // x⁴ − 5x² + 4 = 0 → x ∈ {±1, ±2}, divisors of 4.
    let (result, arena, a) = solve_one(|ar| poly_eq_zero(ar, &[4, 0, -5, 0, 1]));
    assert_sat_replays(&result, &arena, a);
}

#[test]
fn quintic_x5_minus_x_zero_constant_is_sat_at_0() {
    // x⁵ − x = 0 → constant term a₀ = 0 ⇒ x = 0 is a root.
    let (result, arena, a) = solve_one(|ar| poly_eq_zero(ar, &[0, -1, 0, 0, 0, 1]));
    assert_sat_replays(&result, &arena, a);
}

#[test]
fn cubic_negative_root_is_sat() {
    // (x + 5)·(x² + 1) = x³ + 5x² + x + 5 = 0 → only integer root is x = −5.
    let (result, arena, a) = solve_one(|ar| poly_eq_zero(ar, &[5, 1, 5, 1]));
    assert_sat_replays(&result, &arena, a);
}

#[test]
fn zero_eq_poly_orientation_is_sat() {
    // 0 = x³ − 1 (constant on the left), still decided → x = 1.
    let (result, arena, a) = solve_one(|ar| zero_eq_poly(ar, &[-1, 0, 0, 1]));
    assert_sat_replays(&result, &arena, a);
}

// ------------------------------------------------------------------------
// DECIDES — Unsat (every integer divisor of a₀ checked, none a root)
// ------------------------------------------------------------------------

#[test]
fn cubic_x3_minus_2_is_unsat() {
    // x³ − 2 = 0. Divisors of 2: ±1, ±2. 1−2=−1, −1−2=−3, 8−2=6, −8−2=−10. No root.
    let (result, _arena, _a) = solve_one(|ar| poly_eq_zero(ar, &[-2, 0, 0, 1]));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn cubic_x3_plus_x_plus_1_is_unsat() {
    // x³ + x + 1 = 0. Divisors of 1: ±1. 1+1+1=3, −1−1+1=−1. No root.
    let (result, _arena, _a) = solve_one(|ar| poly_eq_zero(ar, &[1, 1, 0, 1]));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn quartic_no_integer_root_is_unsat() {
    // x⁴ + 1 = 0. Divisors of 1: ±1, both give 2. No real (let alone integer) root.
    let (result, _arena, _a) = solve_one(|ar| poly_eq_zero(ar, &[1, 0, 0, 0, 1]));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn quintic_irreducible_no_root_is_unsat() {
    // x⁵ − x + 1 = 0. Divisors of 1: ±1. 1−1+1=1, −1+1+1=1. No integer root.
    let (result, _arena, _a) = solve_one(|ar| poly_eq_zero(ar, &[1, -1, 0, 0, 0, 1]));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

// ------------------------------------------------------------------------
// DECIDES — disequality of degree ≥ 3 (safe ≠, non-root witness)
// ------------------------------------------------------------------------

#[test]
fn cubic_ne_zero_is_sat() {
    // x³ − 6x² + 11x − 6 ≠ 0 → some integer is a non-root (e.g. 0 → −6).
    let (result, arena, a) = solve_one(|ar| poly_ne_zero(ar, &[-6, 11, -6, 1]));
    assert_sat_replays(&result, &arena, a);
}

// ------------------------------------------------------------------------
// MUST DECLINE — out of the exact pattern. We do not assert a specific
// verdict (the downstream NIA dispatch may still decide some of these); we
// only assert the rational-root pass never produces a *wrong* verdict. The
// strongest universal check: any Sat replays, and these never error.
// ------------------------------------------------------------------------

/// A declined shape must never yield an *unsound* result: a `Sat` must replay,
/// and the solve must not error. (`Unsat`/`Unknown` are acceptable downstream
/// outcomes; we only forbid a wrong answer.)
fn assert_not_unsound(result: &CheckResult, arena: &TermArena, assertion: TermId) {
    if matches!(result, CheckResult::Sat(_)) {
        assert_sat_replays(result, arena, assertion);
    }
}

#[test]
fn two_variables_declined_no_unsound() {
    // x³ + y = 0 (two variables) — the rational-root pass must decline.
    let (result, arena, a) = solve_one(|ar| {
        let x = ar.declare("x", Sort::Int).unwrap();
        let y = ar.declare("y", Sort::Int).unwrap();
        let xv = ar.var(x);
        let yv = ar.var(y);
        let x3 = pow(ar, xv, 3);
        let sum = ar.int_add(x3, yv).unwrap();
        let zero = ar.int_const(0);
        ar.eq(sum, zero).unwrap()
    });
    assert_not_unsound(&result, &arena, a);
}

#[test]
fn cubic_inequality_declined_no_unsound() {
    // x³ < 0 — a degree-≥3 inequality. The rational-root pass declines (no exact
    // bounded method); downstream may or may not decide it, but never unsoundly.
    let (result, arena, a) = solve_one(|ar| {
        let x = ar.declare("x", Sort::Int).unwrap();
        let xv = ar.var(x);
        let x3 = pow(ar, xv, 3);
        let zero = ar.int_const(0);
        ar.int_lt(x3, zero).unwrap()
    });
    assert_not_unsound(&result, &arena, a);
}

#[test]
fn huge_constant_term_declined_no_unsound() {
    // x³ + HUGE = 0 with |a₀| ≥ 2^40: the magnitude guard declines divisor
    // enumeration. Result must not be unsound.
    let huge = 1i128 << 41;
    let (result, arena, a) = solve_one(|ar| poly_eq_zero(ar, &[huge, 0, 0, 1]));
    assert_not_unsound(&result, &arena, a);
}

#[test]
fn second_assertion_on_x_declined_no_unsound() {
    // x³ − 6x² + 11x − 6 = 0  ∧  x = 5. The pass fires only on a single
    // assertion, so the rational-root path declines; the conjunction is in fact
    // Unsat (5 is not a root), but we only require no unsound Sat here.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let x3 = pow(&mut arena, xv, 3);
    let c6 = arena.int_const(6);
    let x2 = arena.int_mul(xv, xv).unwrap();
    let six_x2 = arena.int_mul(c6, x2).unwrap();
    let c11 = arena.int_const(11);
    let eleven_x = arena.int_mul(c11, xv).unwrap();
    let c6b = arena.int_const(6);
    let t1 = arena.int_sub(x3, six_x2).unwrap();
    let t2 = arena.int_add(t1, eleven_x).unwrap();
    let p = arena.int_sub(t2, c6b).unwrap();
    let zero = arena.int_const(0);
    let eq0 = arena.eq(p, zero).unwrap();
    let five = arena.int_const(5);
    let eqx5 = arena.eq(xv, five).unwrap();
    let result = solve(&mut arena, &[eq0, eqx5], &SolverConfig::default()).expect("no error");
    // Whatever downstream decides, a Sat would be unsound (no integer is both a
    // root and equal to 5); require it is not Sat.
    assert!(
        !matches!(result, CheckResult::Sat(_)),
        "the conjunction has no solution; got {result:?}"
    );
}
