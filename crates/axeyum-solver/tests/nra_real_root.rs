//! Exact, bounded NRA decision for a single-variable nonlinear-real polynomial
//! constraint `p(x) ⋈ 0`, with **irrational (real-algebraic) witnesses**
//! (ADR-0038, slice 1).
//!
//! Closes the gap `real x*x = 2` → **Sat with witness √2**: the linear-
//! abstraction NRA path abstracts `x·x` to a fresh variable and only ever reports
//! `Unknown`, whereas this decider isolates the real roots of `x² − 2` exactly and
//! returns one as a `Value::RealAlgebraic`. Correctness is everything: every `Sat`
//! is replay-checked (an algebraic witness via `sign_at(p, α) = 0`, a rational
//! witness through the ground evaluator), every `Unsat` is exact by root
//! isolation, and every shape outside the single-variable single-assertion pattern
//! is **declined** (left to the NRA layer) — never mis-decided.

use axeyum_ir::{Rational, Sign, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, solve};

/// Declare a real symbol and return `(its id, a var term)`.
fn real(arena: &mut TermArena, name: &str) -> (SymbolId, TermId) {
    let s = arena.declare(name, Sort::Real).unwrap();
    (s, arena.var(s))
}

/// Build `x*x ⋈ c` (square on the left) over a fresh real `x`, returning the
/// assertion, the arena, and `x`'s symbol id for model inspection.
fn square_cmp(
    c: i128,
    cmp: fn(&mut TermArena, TermId, TermId) -> TermId,
) -> (CheckResult, TermArena, TermId, SymbolId) {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let xx = arena.real_mul(xv, xv).unwrap();
    let k = arena.real_const(Rational::integer(c));
    let assertion = cmp(&mut arena, xx, k);
    let result =
        solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve must not error");
    (result, arena, assertion, xs)
}

fn eq(a: &mut TermArena, l: TermId, r: TermId) -> TermId {
    a.eq(l, r).unwrap()
}
fn ne(a: &mut TermArena, l: TermId, r: TermId) -> TermId {
    let e = a.eq(l, r).unwrap();
    a.not(e).unwrap()
}
fn lt(a: &mut TermArena, l: TermId, r: TermId) -> TermId {
    a.real_lt(l, r).unwrap()
}
fn le(a: &mut TermArena, l: TermId, r: TermId) -> TermId {
    a.real_le(l, r).unwrap()
}
fn gt(a: &mut TermArena, l: TermId, r: TermId) -> TermId {
    a.real_gt(l, r).unwrap()
}

/// The defining polynomial of `x*x = c` is `x² − c` (LSB-first `[-c, 0, 1]`).
fn poly_x2_minus(c: i128) -> Vec<i128> {
    vec![-c, 0, 1]
}

// --- equality: irrational witnesses -------------------------------------------

#[test]
fn square_eq_2_is_sat_with_sqrt2_witness() {
    // THE headline gap: x*x = 2 over ℝ ⇒ Sat with an algebraic witness (±√2).
    let (result, _arena, _t, xs) = square_cmp(2, eq);
    let CheckResult::Sat(model) = &result else {
        panic!("x*x = 2 must be Sat, got {result:?}");
    };
    let x = model.get(xs).expect("model must bind x");
    let alpha = x
        .as_real_algebraic()
        .expect("witness for √2 must be real-algebraic, not a rational");
    // Replay-check (the decider's contract): α is an exact root of x² − 2.
    assert_eq!(
        alpha.sign_at(&poly_x2_minus(2)),
        Some(Sign::Zero),
        "the algebraic witness must satisfy x² − 2 = 0 exactly"
    );
    // And it is genuinely irrational: not equal to any nearby rational.
    assert_ne!(
        alpha.compare_rational(&Rational::new(3, 2)),
        Some(core::cmp::Ordering::Equal)
    );
}

#[test]
fn square_eq_3_is_sat_algebraic() {
    let (result, _arena, _t, xs) = square_cmp(3, eq);
    let CheckResult::Sat(model) = &result else {
        panic!("x*x = 3 must be Sat, got {result:?}");
    };
    let x = model.get(xs).unwrap();
    let alpha = x.as_real_algebraic().expect("√3 is irrational");
    assert_eq!(alpha.sign_at(&poly_x2_minus(3)), Some(Sign::Zero));
}

#[test]
fn square_eq_4_is_sat_rational_two() {
    // x*x = 4 ⇒ x = ±2, an EXACT rational witness (no algebraic number needed).
    let (result, arena, t, xs) = square_cmp(4, eq);
    let CheckResult::Sat(model) = &result else {
        panic!("x*x = 4 must be Sat, got {result:?}");
    };
    let x = model.get(xs).unwrap();
    let q = x
        .as_real()
        .expect("witness for ±2 must be a plain rational");
    assert!(
        q == Rational::integer(2) || q == Rational::integer(-2),
        "x = {q}"
    );
    // A rational witness replays through the ground evaluator on the original.
    let asg = model.to_assignment();
    assert!(matches!(eval(&arena, t, &asg), Ok(Value::Bool(true))));
}

#[test]
fn square_eq_0_is_sat_rational_zero() {
    let (result, arena, t, xs) = square_cmp(0, eq);
    let CheckResult::Sat(model) = &result else {
        panic!("x*x = 0 must be Sat, got {result:?}");
    };
    assert_eq!(model.get(xs), Some(Value::Real(Rational::zero())));
    let asg = model.to_assignment();
    assert!(matches!(eval(&arena, t, &asg), Ok(Value::Bool(true))));
}

#[test]
fn square_eq_neg1_is_unsat() {
    // x*x = −1 has no real root ⇒ exact Unsat.
    let (result, _arena, _t, _xs) = square_cmp(-1, eq);
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

// --- inequalities: rational witnesses (or unsat) ------------------------------

#[test]
fn square_lt_0_is_unsat() {
    // x*x < 0: a square is never negative ⇒ Unsat.
    let (result, _arena, _t, _xs) = square_cmp(0, lt);
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn square_gt_2_is_sat_rational() {
    // x*x > 2: e.g. x = 2 (a rational witness in a +-sign interval).
    let (result, arena, t, xs) = square_cmp(2, gt);
    let CheckResult::Sat(model) = &result else {
        panic!("x*x > 2 must be Sat, got {result:?}");
    };
    let x = model.get(xs).unwrap();
    assert!(x.as_real().is_some(), "inequality witness stays rational");
    let asg = model.to_assignment();
    assert!(matches!(eval(&arena, t, &asg), Ok(Value::Bool(true))));
}

#[test]
fn square_le_0_is_sat_at_origin() {
    // x*x ≤ 0 ⇒ x = 0 (the only solution, a rational root).
    let (result, arena, t, xs) = square_cmp(0, le);
    let CheckResult::Sat(model) = &result else {
        panic!("x*x ≤ 0 must be Sat, got {result:?}");
    };
    assert_eq!(model.get(xs), Some(Value::Real(Rational::zero())));
    let asg = model.to_assignment();
    assert!(matches!(eval(&arena, t, &asg), Ok(Value::Bool(true))));
}

#[test]
fn square_ne_2_is_sat_rational() {
    // x*x ≠ 2: almost everything works; the decider exhibits a rational non-root.
    let (result, arena, t, xs) = square_cmp(2, ne);
    let CheckResult::Sat(model) = &result else {
        panic!("x*x ≠ 2 must be Sat, got {result:?}");
    };
    assert!(model.get(xs).unwrap().as_real().is_some());
    let asg = model.to_assignment();
    assert!(matches!(eval(&arena, t, &asg), Ok(Value::Bool(true))));
}

// --- soundness-negative DECLINE cases (left to NRA, never mis-decided) --------

/// A two-variable product `x*y = 2` is not a single-variable polynomial; the
/// decider declines and the query falls to the NRA layer (which abstracts the
/// product). The result must not be a wrong verdict — Sat or Unknown is fine; we
/// only require it does not crash and is not Unsat (a model exists, e.g. x=y=√2,
/// but the linear abstraction may report Unknown).
#[test]
fn two_variable_product_declines_not_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let p = arena.real_mul(xv, yv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a = arena.eq(p, two).unwrap();
    let r = solve(&mut arena, &[a], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x*y = 2 is satisfiable; got {r:?}"
    );
}

/// A second assertion could constrain `x`, so the decider declines (it fires only
/// on a single-assertion query). `x*x = 4 ∧ x = 2` is satisfiable; the engines
/// below decide it, and the verdict must not be Unsat.
#[test]
fn second_assertion_declines_not_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let xx = arena.real_mul(xv, xv).unwrap();
    let four = arena.real_const(Rational::integer(4));
    let a1 = arena.eq(xx, four).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a2 = arena.eq(xv, two).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x*x=4 ∧ x=2 is sat; got {r:?}"
    );
}

// --- higher-degree equations: degree ≥ 3 must decide (regression) -------------
//
// These guard the slice-1 coverage gap: `isolate_one`'s bisection previously
// `?`-declined the *whole* root the moment a midpoint Horner evaluation
// overflowed `i128` (denominators grow like `2^depth`, raised to the polynomial
// degree). Every single-variable real equation of degree ≥ 3 therefore degraded
// to `Unknown`. The fix stops refining on overflow and keeps the last valid
// isolating bracket. Each `Sat` below is replay-checked: an algebraic witness via
// `sign_at(p, α) = 0`, a rational witness via the ground evaluator.

/// `x*x*x` (cubed) over a fresh real `x`.
fn cube(arena: &mut TermArena, xv: TermId) -> TermId {
    let xx = arena.real_mul(xv, xv).unwrap();
    arena.real_mul(xx, xv).unwrap()
}

#[test]
fn cube_eq_2_is_sat_with_cbrt2_witness() {
    // x*x*x = 2 ⇒ x = ∛2, irrational ⇒ Sat with an algebraic witness.
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let xxx = cube(&mut arena, xv);
    let two = arena.real_const(Rational::integer(2));
    let a = arena.eq(xxx, two).unwrap();
    let r = solve(&mut arena, &[a], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x*x*x = 2 must be Sat, got {r:?}");
    };
    let x = model.get(xs).unwrap();
    let alpha = x
        .as_real_algebraic()
        .expect("∛2 is irrational ⇒ algebraic witness");
    // Replay-check: α is an exact root of x³ − 2 (LSB-first [-2, 0, 0, 1]).
    assert_eq!(
        alpha.sign_at(&[-2, 0, 0, 1]),
        Some(Sign::Zero),
        "the algebraic witness must satisfy x³ − 2 = 0 exactly"
    );
}

#[test]
fn quartic_biquadratic_eq_0_is_sat() {
    // x⁴ − 5x² + 6 = 0 ⇒ roots ±√2, ±√3. LSB-first [6, 0, -5, 0, 1].
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let xx = arena.real_mul(xv, xv).unwrap();
    let x4 = arena.real_mul(xx, xx).unwrap();
    let five = arena.real_const(Rational::integer(5));
    let five_xx = arena.real_mul(five, xx).unwrap();
    let lhs = arena.real_sub(x4, five_xx).unwrap();
    let six = arena.real_const(Rational::integer(6));
    let lhs = arena.real_add(lhs, six).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a = arena.eq(lhs, zero).unwrap();
    let r = solve(&mut arena, &[a], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x⁴ − 5x² + 6 = 0 must be Sat, got {r:?}");
    };
    // Witness is one of ±√2, ±√3, all irrational ⇒ algebraic, replay-checked.
    let x = model.get(xs).unwrap();
    let alpha = x
        .as_real_algebraic()
        .expect("root is irrational ⇒ algebraic witness");
    assert_eq!(
        alpha.sign_at(&[6, 0, -5, 0, 1]),
        Some(Sign::Zero),
        "the witness must satisfy x⁴ − 5x² + 6 = 0 exactly"
    );
}

#[test]
fn cube_minus_x_eq_0_is_sat_rational() {
    // x*x*x − x = 0 ⇒ x(x−1)(x+1) = 0, roots {0, ±1}, all rational.
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let xxx = cube(&mut arena, xv);
    let lhs = arena.real_sub(xxx, xv).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a = arena.eq(lhs, zero).unwrap();
    let r = solve(&mut arena, &[a], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x³ − x = 0 must be Sat, got {r:?}");
    };
    let q = model
        .get(xs)
        .unwrap()
        .as_real()
        .expect("a root of x³ − x is rational (0 or ±1)");
    assert!(
        q == Rational::zero() || q == Rational::integer(1) || q == Rational::integer(-1),
        "x = {q}"
    );
    // A rational witness replays through the ground evaluator on the original.
    let asg = model.to_assignment();
    assert!(matches!(eval(&arena, a, &asg), Ok(Value::Bool(true))));
}

#[test]
fn cube_eq_neg8_is_sat_rational_neg2() {
    // x*x*x = −8 ⇒ x = −2 (the unique real root, rational).
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let xxx = cube(&mut arena, xv);
    let k = arena.real_const(Rational::integer(-8));
    let a = arena.eq(xxx, k).unwrap();
    let r = solve(&mut arena, &[a], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x³ = −8 must be Sat, got {r:?}");
    };
    assert_eq!(model.get(xs), Some(Value::Real(Rational::integer(-2))));
    let asg = model.to_assignment();
    assert!(matches!(eval(&arena, a, &asg), Ok(Value::Bool(true))));
}

// --- higher-degree equations with NO real root: exact Unsat -------------------

#[test]
fn quartic_x2_plus_1_eq_0_is_unsat() {
    // x² + 1 = 0 has no real root ⇒ exact Unsat (sanity for the degree-2 path).
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let xx = arena.real_mul(xv, xv).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let lhs = arena.real_add(xx, one).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a = arena.eq(lhs, zero).unwrap();
    let r = solve(&mut arena, &[a], &SolverConfig::default()).expect("no error");
    assert!(matches!(r, CheckResult::Unsat), "x² + 1 = 0; got {r:?}");
}

#[test]
fn quartic_x4_plus_1_eq_0_is_unsat() {
    // x⁴ + 1 = 0 has no real root (x⁴ ≥ 0 ⇒ x⁴ + 1 ≥ 1) ⇒ exact Unsat.
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let xx = arena.real_mul(xv, xv).unwrap();
    let x4 = arena.real_mul(xx, xx).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let lhs = arena.real_add(x4, one).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a = arena.eq(lhs, zero).unwrap();
    let r = solve(&mut arena, &[a], &SolverConfig::default()).expect("no error");
    assert!(matches!(r, CheckResult::Unsat), "x⁴ + 1 = 0; got {r:?}");
}

// --- higher-degree inequality: rational witness via sign-interval sampling ----

#[test]
fn cube_gt_5_is_sat_rational() {
    // x*x*x > 5: e.g. x = 2 (2³ = 8 > 5). The inequality arm samples a rational in
    // a +-sign interval; the witness must stay rational and replay.
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let xxx = cube(&mut arena, xv);
    let five = arena.real_const(Rational::integer(5));
    let a = arena.real_gt(xxx, five).unwrap();
    let r = solve(&mut arena, &[a], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x³ > 5 must be Sat, got {r:?}");
    };
    assert!(
        model.get(xs).unwrap().as_real().is_some(),
        "inequality witness stays rational"
    );
    let asg = model.to_assignment();
    assert!(matches!(eval(&arena, a, &asg), Ok(Value::Bool(true))));
}

// --- CONJUNCTIONS over one shared variable: sign-cell decomposition -----------
//
// The whole query is `C₁ ∧ … ∧ Cₘ`, each `pᵢ(x) ⋈ᵢ 0` over the SAME real `x`.
// Decided exactly by testing the roots of all `pᵢ` plus one rational sample per
// open cell; every `Sat` is replay-checked against ALL assertions.

/// `x*x = 2 ∧ x < 0` ⇒ Sat with the **negative** algebraic root −√2.
#[test]
fn conj_square_eq_2_and_negative_is_sat_neg_sqrt2() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(xx, two).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a2 = arena.real_lt(xv, zero).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x*x=2 ∧ x<0 must be Sat, got {r:?}");
    };
    let x = model.get(xs).unwrap();
    let alpha = x.as_real_algebraic().expect("−√2 is irrational");
    // It is a root of x²−2 …
    assert_eq!(alpha.sign_at(&poly_x2_minus(2)), Some(Sign::Zero));
    // … and it is the NEGATIVE one (< 0).
    assert_eq!(
        alpha.compare_rational(&Rational::zero()),
        Some(core::cmp::Ordering::Less),
        "the witness must be the negative root −√2"
    );
}

/// `x*x = 2 ∧ x > 0` ⇒ Sat with the **positive** algebraic root +√2.
#[test]
fn conj_square_eq_2_and_positive_is_sat_pos_sqrt2() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(xx, two).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a2 = arena.real_gt(xv, zero).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x*x=2 ∧ x>0 must be Sat, got {r:?}");
    };
    let alpha = model.get(xs).unwrap();
    let alpha = alpha.as_real_algebraic().expect("+√2 is irrational");
    assert_eq!(alpha.sign_at(&poly_x2_minus(2)), Some(Sign::Zero));
    assert_eq!(
        alpha.compare_rational(&Rational::zero()),
        Some(core::cmp::Ordering::Greater),
        "the witness must be the positive root +√2"
    );
}

/// `x*x = 2 ∧ x > 0 ∧ x < 2` ⇒ Sat (+√2 ≈ 1.41 ∈ (0, 2)).
#[test]
fn conj_square_eq_2_positive_bounded_is_sat() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(xx, two).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a2 = arena.real_gt(xv, zero).unwrap();
    let twoc = arena.real_const(Rational::integer(2));
    let a3 = arena.real_lt(xv, twoc).unwrap();
    let r = solve(&mut arena, &[a1, a2, a3], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x*x=2 ∧ x>0 ∧ x<2 must be Sat, got {r:?}");
    };
    let alpha = model.get(xs).unwrap();
    let alpha = alpha.as_real_algebraic().expect("+√2 is irrational");
    assert_eq!(alpha.sign_at(&poly_x2_minus(2)), Some(Sign::Zero));
}

/// `x*x = 2 ∧ x < −2` ⇒ Unsat: the only roots are ±√2 ≈ ±1.41, and −√2 ≮ −2.
#[test]
fn conj_square_eq_2_and_lt_neg2_is_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(xx, two).unwrap();
    let neg2 = arena.real_const(Rational::integer(-2));
    let a2 = arena.real_lt(xv, neg2).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        matches!(r, CheckResult::Unsat),
        "x*x=2 ∧ x<−2 has no real solution; got {r:?}"
    );
}

/// `x³ > 1 ∧ x < 2` ⇒ Sat with a **rational** witness in the open cell (e.g. 1.5).
#[test]
fn conj_cube_gt_1_and_lt_2_is_sat_rational() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let xxx = cube(&mut arena, xv);
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.real_gt(xxx, one).unwrap();
    let twoc = arena.real_const(Rational::integer(2));
    let a2 = arena.real_lt(xv, twoc).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x³>1 ∧ x<2 must be Sat, got {r:?}");
    };
    assert!(
        model.get(xs).unwrap().as_real().is_some(),
        "inequality-only conjunction has a rational witness"
    );
    let asg = model.to_assignment();
    assert!(matches!(eval(&arena, a1, &asg), Ok(Value::Bool(true))));
    assert!(matches!(eval(&arena, a2, &asg), Ok(Value::Bool(true))));
}

/// `1 < x ∧ x < 2 ∧ x*x ≠ 2` ⇒ Sat with a rational witness (any rational in
/// (1, 2) other than the irrational √2, e.g. 3/2, works).
#[test]
fn conj_bounded_and_ne_sqrt2_is_sat_rational() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.real_lt(one, xv).unwrap();
    let twoc = arena.real_const(Rational::integer(2));
    let a2 = arena.real_lt(xv, twoc).unwrap();
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let eqp = arena.eq(xx, two).unwrap();
    let a3 = arena.not(eqp).unwrap();
    let r = solve(&mut arena, &[a1, a2, a3], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("1<x ∧ x<2 ∧ x*x≠2 must be Sat, got {r:?}");
    };
    let q = model
        .get(xs)
        .unwrap()
        .as_real()
        .expect("witness stays rational");
    // Replay against all three assertions.
    let asg = model.to_assignment();
    for a in [a1, a2, a3] {
        assert!(matches!(eval(&arena, a, &asg), Ok(Value::Bool(true))));
    }
    assert_ne!(q, Rational::integer(2)); // sanity
}

/// A top-level `and` of two single-variable real constraints (as ONE assertion)
/// is flattened the same way as a two-assertion list.
#[test]
fn conj_as_single_and_term_is_sat() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(xx, two).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a2 = arena.real_gt(xv, zero).unwrap();
    let conj = arena.and(a1, a2).unwrap();
    let r = solve(&mut arena, &[conj], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("(x*x=2 ∧ x>0) as one `and` must be Sat, got {r:?}");
    };
    let alpha = model.get(xs).unwrap();
    let alpha = alpha.as_real_algebraic().expect("+√2 is irrational");
    assert_eq!(alpha.sign_at(&poly_x2_minus(2)), Some(Sign::Zero));
    assert_eq!(
        alpha.compare_rational(&Rational::zero()),
        Some(core::cmp::Ordering::Greater)
    );
}

// --- conjunction soundness-negative DECLINE cases -----------------------------

/// `x*y = 2 ∧ x > 0` mixes two variables; the decider declines (left to NRA).
/// It is satisfiable (x = y = √2), so the verdict must NOT be Unsat.
#[test]
fn conj_two_variables_declines_not_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let p = arena.real_mul(xv, yv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(p, two).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a2 = arena.real_gt(xv, zero).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x*y=2 ∧ x>0 is sat; got {r:?}"
    );
}

/// A conjunction containing a non-polynomial atom (real division) declines: the
/// whole query is left to NRA, never mis-decided. It is satisfiable (x = 2), so
/// the verdict must NOT be Unsat.
#[test]
fn conj_with_nonpoly_atom_declines_not_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let xx = arena.real_mul(xv, xv).unwrap();
    let four = arena.real_const(Rational::integer(4));
    let a1 = arena.eq(xx, four).unwrap();
    // A non-polynomial real-division atom: x / x = 1 (collector declines on div).
    let div = arena.real_div(xv, xv).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a2 = arena.eq(div, one).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x*x=4 ∧ x/x=1 is sat (x=2); got {r:?}"
    );
}

// --- MULTIVARIATE decomposition: linear substitution + independent components -
//
// The query has ≥ 2 distinct variables; the single-variable decider declines and
// the sound, bounded multivariate decomposition fires: a variable defined by a
// linear equality `y = L(others)` is substituted out (fixpoint), and the
// remaining atoms that share no variable are decided independently. Every `Sat`
// is replay-checked against the FULL multivariate model on ALL assertions.

/// `x*x = 2 ∧ y = −x` ⇒ substitute `y := −x` → single-variable `x*x = 2`, decide
/// `x = ±√2`, then `y = −x`. Sat with `y = ∓√2` consistent. Replay-checked.
#[test]
fn multi_subst_y_eq_neg_x_is_sat() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let (ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(xx, two).unwrap();
    // y = −x.
    let negx = arena.real_neg(xv).unwrap();
    let a2 = arena.eq(yv, negx).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x*x=2 ∧ y=−x must be Sat, got {r:?}");
    };
    // Both x and y are bound to the (irrational) algebraic ±√2 / ∓√2.
    let x = model.get(xs).unwrap();
    let y = model.get(ys).unwrap();
    let ax = x.as_real_algebraic().expect("x is √2 / −√2");
    let ay = y.as_real_algebraic().expect("y is −√2 / √2");
    assert_eq!(ax.sign_at(&poly_x2_minus(2)), Some(Sign::Zero));
    assert_eq!(ay.sign_at(&poly_x2_minus(2)), Some(Sign::Zero));
    // y = −x: they are on opposite sides of zero.
    let xc = ax.compare_rational(&Rational::zero()).unwrap();
    let yc = ay.compare_rational(&Rational::zero()).unwrap();
    assert_ne!(xc, yc, "y = −x must have the opposite sign of x");
    assert_ne!(xc, core::cmp::Ordering::Equal);
}

/// `x*x = 2 ∧ z*z = 3` ⇒ x and z are independent ⇒ Sat with x = ±√2, z = ±√3.
#[test]
fn multi_independent_components_is_sat() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let (zs, zv) = real(&mut arena, "z");
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(xx, two).unwrap();
    let zz = arena.real_mul(zv, zv).unwrap();
    let three = arena.real_const(Rational::integer(3));
    let a2 = arena.eq(zz, three).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x*x=2 ∧ z*z=3 must be Sat, got {r:?}");
    };
    let ax = model.get(xs).unwrap();
    let az = model.get(zs).unwrap();
    assert_eq!(
        ax.as_real_algebraic().unwrap().sign_at(&poly_x2_minus(2)),
        Some(Sign::Zero)
    );
    assert_eq!(
        az.as_real_algebraic().unwrap().sign_at(&poly_x2_minus(3)),
        Some(Sign::Zero)
    );
}

/// `x*x = 2 ∧ y = x ∧ y < 0` ⇒ substitute `y := x` → `x*x = 2 ∧ x < 0` →
/// x = −√2, y = −√2. Sat. Replay-checked (y is the negative algebraic root).
#[test]
fn multi_subst_y_eq_x_with_bound_is_sat() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let (ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(xx, two).unwrap();
    let a2 = arena.eq(yv, xv).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a3 = arena.real_lt(yv, zero).unwrap();
    let r = solve(&mut arena, &[a1, a2, a3], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x*x=2 ∧ y=x ∧ y<0 must be Sat, got {r:?}");
    };
    let ax = model.get(xs).unwrap();
    let ay = model.get(ys).unwrap();
    let ax = ax.as_real_algebraic().expect("x = −√2");
    let ay = ay.as_real_algebraic().expect("y = −√2");
    assert_eq!(ax.sign_at(&poly_x2_minus(2)), Some(Sign::Zero));
    assert_eq!(ay.sign_at(&poly_x2_minus(2)), Some(Sign::Zero));
    // Both are the NEGATIVE root.
    assert_eq!(
        ax.compare_rational(&Rational::zero()),
        Some(core::cmp::Ordering::Less)
    );
    assert_eq!(
        ay.compare_rational(&Rational::zero()),
        Some(core::cmp::Ordering::Less)
    );
}

/// `x*x = 2 ∧ y = x + 1 ∧ y > 2` ⇒ substitute `y := x + 1`. `y > 2 ⇔ x > 1`, so
/// x = +√2 (≈ 1.41 > 1), y = √2 + 1 (≈ 2.41 > 2). Sat, replay-checked.
#[test]
fn multi_subst_affine_definition_is_sat() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let (ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(xx, two).unwrap();
    // y = x + 1.
    let one = arena.real_const(Rational::integer(1));
    let xp1 = arena.real_add(xv, one).unwrap();
    let a2 = arena.eq(yv, xp1).unwrap();
    // y > 2.
    let twoc = arena.real_const(Rational::integer(2));
    let a3 = arena.real_gt(yv, twoc).unwrap();
    let r = solve(&mut arena, &[a1, a2, a3], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x*x=2 ∧ y=x+1 ∧ y>2 must be Sat, got {r:?}");
    };
    let ax = model.get(xs).unwrap();
    let ax = ax.as_real_algebraic().expect("x = +√2");
    assert_eq!(ax.sign_at(&poly_x2_minus(2)), Some(Sign::Zero));
    // x must be the POSITIVE root (x > 1).
    assert_eq!(
        ax.compare_rational(&Rational::integer(1)),
        Some(core::cmp::Ordering::Greater)
    );
    // y is bound to the derived algebraic value √2 + 1, which is > 2.
    let ay = model.get(ys).unwrap();
    let ay = ay.as_real_algebraic().expect("y = √2 + 1 is irrational");
    assert_eq!(
        ay.compare_rational(&Rational::integer(2)),
        Some(core::cmp::Ordering::Greater),
        "y = √2 + 1 ≈ 2.41 > 2"
    );
}

/// `x*x = 2 ∧ y = x ∧ y*y < 1` ⇒ substitute `y := x`: `x*x = 2 ∧ x*x < 1`,
/// which is Unsat (x² cannot be both 2 and < 1). A multivariate UNSAT via a
/// decomposed single-variable sub-system. Exact.
#[test]
fn multi_subst_to_unsat_subsystem() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(xx, two).unwrap();
    let a2 = arena.eq(yv, xv).unwrap();
    let yy = arena.real_mul(yv, yv).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a3 = arena.real_lt(yy, one).unwrap();
    let r = solve(&mut arena, &[a1, a2, a3], &SolverConfig::default()).expect("no error");
    assert!(
        matches!(r, CheckResult::Unsat),
        "x*x=2 ∧ y=x ∧ y*y<1 is Unsat; got {r:?}"
    );
}

/// `x*x = 2 ∧ y = x ∧ x = 3` ⇒ substitute `y := x`, leaving `x*x = 2 ∧ x = 3`;
/// substitute `x := 3` (it is a linear definition too) — but x is the live var of
/// `x*x=2`. Easier: `x*x=2 ∧ x=3` is a single-variable system → Unsat (3² ≠ 2).
/// Confirms substitution + single-var Unsat compose.
#[test]
fn multi_subst_chain_to_single_var_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(xx, two).unwrap();
    let a2 = arena.eq(yv, xv).unwrap();
    let three = arena.real_const(Rational::integer(3));
    let a3 = arena.eq(xv, three).unwrap();
    let r = solve(&mut arena, &[a1, a2, a3], &SolverConfig::default()).expect("no error");
    assert!(
        matches!(r, CheckResult::Unsat),
        "x*x=2 ∧ y=x ∧ x=3 is Unsat; got {r:?}"
    );
}

/// Independent rational components: `x = 1 ∧ z*z = 4` ⇒ x = 1, z = ±2, both
/// rational, decided independently. Sat, replay-checked.
#[test]
fn multi_independent_rational_is_sat() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let (zs, zv) = real(&mut arena, "z");
    // x*x = 1 keeps x as a genuine variable in a degree-2 component.
    let xx = arena.real_mul(xv, xv).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.eq(xx, one).unwrap();
    let zz = arena.real_mul(zv, zv).unwrap();
    let four = arena.real_const(Rational::integer(4));
    let a2 = arena.eq(zz, four).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x*x=1 ∧ z*z=4 must be Sat, got {r:?}");
    };
    let qx = model.get(xs).unwrap().as_real().expect("x rational");
    let qz = model.get(zs).unwrap().as_real().expect("z rational");
    assert!(qx == Rational::integer(1) || qx == Rational::integer(-1));
    assert!(qz == Rational::integer(2) || qz == Rational::integer(-2));
    // Replay both assertions through the ground evaluator.
    let asg = model.to_assignment();
    assert!(matches!(eval(&arena, a1, &asg), Ok(Value::Bool(true))));
    assert!(matches!(eval(&arena, a2, &asg), Ok(Value::Bool(true))));
}

// --- multivariate DECLINE cases (coupled / CAD — never mis-decided) -----------

/// `x*y = 2 ∧ x > 0` is genuinely coupled (a product of two distinct variables
/// with no linear definition to substitute). The decider DECLINES; the result
/// must not be a wrong verdict. It is satisfiable (x = y = √2) ⇒ not Unsat.
#[test]
fn multi_coupled_product_declines_not_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xy = arena.real_mul(xv, yv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(xy, two).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a2 = arena.real_gt(xv, zero).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x*y=2 ∧ x>0 is sat (deferred CAD); got {r:?}"
    );
}

/// The circle/line system `x² + y² = 1 ∧ x + y = 1` is satisfiable
/// (e.g. (1, 0) or (0, 1)). After substituting `y := 1 − x` it becomes the
/// single-variable `x² + (1−x)² = 1 ⇔ 2x² − 2x = 0 ⇔ x(x−1)=0`, which IS in scope
/// (a single-variable component). So this one is actually DECIDED Sat — verify it
/// is not Unsat (soundness), and the model replays.
#[test]
fn multi_circle_line_substitutes_to_single_var_sat() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let (ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let yy = arena.real_mul(yv, yv).unwrap();
    let sum_sq = arena.real_add(xx, yy).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.eq(sum_sq, one).unwrap();
    // x + y = 1.
    let xpy = arena.real_add(xv, yv).unwrap();
    let onec = arena.real_const(Rational::integer(1));
    let a2 = arena.eq(xpy, onec).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    // It is satisfiable, so it must NOT be Unsat. (The substitution lands it in
    // scope, so we expect Sat; at minimum, never a wrong Unsat.)
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x²+y²=1 ∧ x+y=1 is sat (e.g. (1,0)); got {r:?}"
    );
    if let CheckResult::Sat(model) = &r {
        // Replay: both vars rational here (roots 0/1), ground evaluator decides.
        let asg = model.to_assignment();
        assert!(matches!(eval(&arena, a1, &asg), Ok(Value::Bool(true))));
        assert!(matches!(eval(&arena, a2, &asg), Ok(Value::Bool(true))));
        let _ = (xs, ys);
    }
}

/// A genuinely coupled nonlinear system with NO substitutable linear definition:
/// `x² + y² = 1 ∧ x*y = 1`. No linear equality ⇒ no substitution; the component
/// couples x and y nonlinearly with TWO equalities ⇒ the resultant-elimination
/// slice fires. `Res_y(x²+y²−1, xy−1) = x⁴ − x² + 1` has NO real root, so the two
/// equalities have no common real solution ⇒ **Unsat** (exact). Soundness: an
/// empty equality variety stays empty.
#[test]
fn multi_coupled_nonlinear_unsat_via_resultant() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let yy = arena.real_mul(yv, yv).unwrap();
    let sum_sq = arena.real_add(xx, yy).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.eq(sum_sq, one).unwrap();
    let xy = arena.real_mul(xv, yv).unwrap();
    let onec = arena.real_const(Rational::integer(1));
    let a2 = arena.eq(xy, onec).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        matches!(r, CheckResult::Unsat),
        "x²+y²=1 ∧ x*y=1 is unsat (x⁴−x²+1 has no real root); got {r:?}"
    );
}

/// A coupled 2-variable system WITH a real solution, decided Sat by the resultant
/// slice and replay-checked: `x² + y² = 2 ∧ x*y = 1`. Common real solutions are
/// (1,1) and (−1,−1) (both rational). `Res_y = x⁴ − 2x² + 1 = (x²−1)²`, roots
/// x = ±1; lifting x=1 gives y=1. The model replays against both equalities.
#[test]
fn multi_coupled_nonlinear_sat_via_resultant() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let (ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let yy = arena.real_mul(yv, yv).unwrap();
    let sum_sq = arena.real_add(xx, yy).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(sum_sq, two).unwrap();
    let xy = arena.real_mul(xv, yv).unwrap();
    let onec = arena.real_const(Rational::integer(1));
    let a2 = arena.eq(xy, onec).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x²+y²=2 ∧ x*y=1 must be Sat (e.g. (1,1)); got {r:?}");
    };
    // Replay: the witness satisfies BOTH original equalities exactly.
    let asg = model.to_assignment();
    assert!(
        matches!(eval(&arena, a1, &asg), Ok(Value::Bool(true))),
        "x²+y²=2 must hold at the witness"
    );
    assert!(
        matches!(eval(&arena, a2, &asg), Ok(Value::Bool(true))),
        "x*y=1 must hold at the witness"
    );
    // Both coordinates are rational here (±1).
    let x = model.get(xs).unwrap().as_real().expect("x rational");
    let y = model.get(ys).unwrap().as_real().expect("y rational");
    assert_eq!(
        x.checked_mul(y),
        Some(Rational::integer(1)),
        "x*y must equal 1, got x={x}, y={y}"
    );
}

/// A coupled, all-nonlinear, all-equality system whose resultant has **rational**
/// real roots but where a third equality rules every common root out ⇒ **Unsat**
/// by exhaustive enumeration. `x² + y² = 2 ∧ x*y = 1 ∧ x² + y² = 5`: the first two
/// have common roots (±1, ±1); none satisfies x² + y² = 5 (each gives 2). All
/// atoms are equalities and every x-candidate is rational, so the enumeration is
/// provably exhaustive ⇒ Unsat. (All atoms are degree-2, so the substitution path
/// never breaks the coupling — this routes through the resultant slice.)
#[test]
fn multi_coupled_exhaustive_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let yy = arena.real_mul(yv, yv).unwrap();
    let sum_sq = arena.real_add(xx, yy).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(sum_sq, two).unwrap();
    let xy = arena.real_mul(xv, yv).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a2 = arena.eq(xy, one).unwrap();
    // A second circle of a different radius: x² + y² = 5 (rebuilt to a fresh term).
    let xx2 = arena.real_mul(xv, xv).unwrap();
    let yy2 = arena.real_mul(yv, yv).unwrap();
    let sum_sq2 = arena.real_add(xx2, yy2).unwrap();
    let five = arena.real_const(Rational::integer(5));
    let a3 = arena.eq(sum_sq2, five).unwrap();
    let r = solve(&mut arena, &[a1, a2, a3], &SolverConfig::default()).expect("no error");
    assert!(
        matches!(r, CheckResult::Unsat),
        "x²+y²=2 ∧ x*y=1 ∧ x²+y²=5 is unsat (common roots (±1,±1) give x²+y²=2≠5); got {r:?}"
    );
}

/// Region-only coupled system: `x*y > 1 ∧ x > 0`. There is only ONE (in fact
/// zero) equality, so the resultant slice has no eliminable pair ⇒ DECLINE. The
/// satisfying set is a 2-D region; the decider must NOT answer Unsat (it is sat,
/// e.g. x=2, y=1).
#[test]
fn multi_region_only_declines_not_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xy = arena.real_mul(xv, yv).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.real_gt(xy, one).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a2 = arena.real_gt(xv, zero).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x*y>1 ∧ x>0 is sat (region; e.g. (2,1)); got {r:?}"
    );
}

// --- ALGEBRAIC (α, β) grid-lift slice (CAD/nlsat step 3) ----------------------

/// Algebraic-coupled SAT via the (α, β) grid lift (was `Unknown`): the diagonal of
/// a circle, `x² + y² = 4 ∧ x = y`, whose only real solutions are `x = y = ±√2`
/// (irrational). The witness's `(√2, √2)` coordinates are algebraic; the engine
/// decides **Sat** and the model satisfies BOTH original assertions under the
/// independent ground evaluator (a genuine replay of `x²+y²=4` and `x=y`).
#[test]
fn grid_circle_diagonal_sat_sqrt2() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let (ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let yy = arena.real_mul(yv, yv).unwrap();
    let sum_sq = arena.real_add(xx, yy).unwrap();
    let four = arena.real_const(Rational::integer(4));
    let a1 = arena.eq(sum_sq, four).unwrap();
    let a2 = arena.eq(xv, yv).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x²+y²=4 ∧ x=y must be Sat with x=y=±√2; got {r:?}");
    };
    // Independent replay: BOTH original assertions hold at the witness.
    let asg = model.to_assignment();
    assert!(
        matches!(eval(&arena, a1, &asg), Ok(Value::Bool(true))),
        "x²+y²=4 must hold at the algebraic witness"
    );
    assert!(
        matches!(eval(&arena, a2, &asg), Ok(Value::Bool(true))),
        "x=y must hold at the algebraic witness"
    );
    // The witness is genuinely algebraic (irrational ±√2), not a rational.
    assert!(
        model.get(xs).unwrap().as_real_algebraic().is_some(),
        "x must be an algebraic (irrational) value"
    );
    assert!(
        model.get(ys).unwrap().as_real_algebraic().is_some(),
        "y must be an algebraic (irrational) value"
    );
    // The square of the witness is exactly 2: x·x − 2 vanishes by exact sign.
    let x = model.get(xs).unwrap();
    let a = x.as_real_algebraic().unwrap();
    assert_eq!(
        a.sign_at(&[-2, 0, 1]),
        Some(Sign::Zero),
        "x must satisfy x² = 2 exactly"
    );
}

/// Algebraic-coupled SAT via the grid, mixing a univariate and a bivariate
/// equality: `x² = 2 ∧ x*y = 1`. The unique-up-to-sign solutions are
/// `x = ±√2, y = ±1/√2` (both irrational). x-candidates come from the univariate
/// `x²−2`; y-candidates from `Res_x(x²−2, xy−1)`. The grid pair test (exact field
/// arithmetic, e.g. `√2 · 1/√2 = 1`) certifies **Sat**; the model replays.
#[test]
fn grid_univar_bivar_sat_recip_sqrt2() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let (ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(xx, two).unwrap();
    let xy = arena.real_mul(xv, yv).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a2 = arena.eq(xy, one).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x²=2 ∧ x*y=1 must be Sat with x=±√2, y=±1/√2; got {r:?}");
    };
    let asg = model.to_assignment();
    assert!(
        matches!(eval(&arena, a1, &asg), Ok(Value::Bool(true))),
        "x²=2 must hold at the witness"
    );
    assert!(
        matches!(eval(&arena, a2, &asg), Ok(Value::Bool(true))),
        "x*y=1 must hold at the algebraic witness (√2 · 1/√2 = 1)"
    );
    // Both coordinates are genuinely algebraic.
    assert!(model.get(xs).unwrap().as_real_algebraic().is_some());
    assert!(model.get(ys).unwrap().as_real_algebraic().is_some());
}

/// Algebraic-coupled UNSAT via the grid, certified EXHAUSTIVELY (all equalities,
/// algebraic candidates): `x² = 2 ∧ y² = 2 ∧ x*y = −3`. The candidate coordinates
/// are `x, y = ±√2`, so `x*y ∈ {2, −2}` — never `−3`. Every atom is an equality
/// and the grid is the complete common-solution candidate set, so the engine
/// certifies **Unsat** (not Unknown) even though the coordinates are algebraic.
#[test]
fn grid_algebraic_exhaustive_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(xx, two).unwrap();
    let yy = arena.real_mul(yv, yv).unwrap();
    let two2 = arena.real_const(Rational::integer(2));
    let a2 = arena.eq(yy, two2).unwrap();
    let xy = arena.real_mul(xv, yv).unwrap();
    let neg3 = arena.real_const(Rational::integer(-3));
    let a3 = arena.eq(xy, neg3).unwrap();
    let r = solve(&mut arena, &[a1, a2, a3], &SolverConfig::default()).expect("no error");
    assert!(
        matches!(r, CheckResult::Unsat),
        "x²=2 ∧ y²=2 ∧ x*y=−3 is unsat (±√2·±√2 ∈ {{2,−2}} ≠ −3), certified by the \
         algebraic grid; got {r:?}"
    );
}

/// Algebraic-coupled UNSAT for the classic circle/line-too-far system, all
/// equalities: `x² + y² = 1 ∧ x = y + 2`. Substituting the line gives
/// `2y² + 4y + 3 = 0` whose discriminant `16 − 24 < 0` ⇒ NO real solution. The
/// engine certifies **Unsat** (the resultant has no real root) rather than
/// Unknown.
#[test]
fn grid_circle_line_too_far_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let yy = arena.real_mul(yv, yv).unwrap();
    let sum_sq = arena.real_add(xx, yy).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.eq(sum_sq, one).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let yp2 = arena.real_add(yv, two).unwrap();
    let a2 = arena.eq(xv, yp2).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        matches!(r, CheckResult::Unsat),
        "x²+y²=1 ∧ x=y+2 is unsat (line too far from the unit circle); got {r:?}"
    );
}

/// A 2-variable component WITH an inequality must NEVER be wrongly Unsat from the
/// grid (a region is not captured by point candidates). `x² = 2 ∧ x*y = 1 ∧ y > 0`
/// IS satisfiable (`x=√2, y=1/√2 > 0`). The grid decline path leaves the
/// inequality component to the outer engine ⇒ the verdict is Sat or Unknown, but
/// crucially NOT a (wrong) Unsat.
#[test]
fn grid_inequality_component_not_wrongly_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(xx, two).unwrap();
    let xy = arena.real_mul(xv, yv).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a2 = arena.eq(xy, one).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a3 = arena.real_gt(yv, zero).unwrap();
    let r = solve(&mut arena, &[a1, a2, a3], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x²=2 ∧ x*y=1 ∧ y>0 is sat (x=√2, y=1/√2>0); must NOT be wrongly Unsat; got {r:?}"
    );
}

/// A genuinely coupled equality system with deeply-nested-radical witnesses:
/// `x² + y² = 4 ∧ x*y = 1`. `Res_y = x⁴ − 4x² + 1` whose roots are `±√(2±√3)`
/// (degree-4 algebraic, all irrational). Real solutions are
/// `(x, y) = (±√(2+√3), ±√(2−√3))` and their swaps (same sign).
///
/// With arbitrary-precision `RealAlgebraic` storage (ADR-0045) the algebraic
/// (α, β) grid lift now DECIDES this **Sat**: the grid's algebraic x/y candidates
/// are tested by exact bignum field arithmetic — `x² + y² = (2+√3)+(2−√3) = 4` and
/// `x·y = √(2+√3)·√(2−√3) = √(4−3) = 1` — with no i128-storage overflow. The
/// returned model is independently replay-checked here: evaluating BOTH original
/// assertions through the IR ground evaluator at the witness yields `true`.
#[test]
fn multi_coupled_algebraic_x_decides_sat_with_replay() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let (ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let yy = arena.real_mul(yv, yv).unwrap();
    let sum_sq = arena.real_add(xx, yy).unwrap();
    let four = arena.real_const(Rational::integer(4));
    let a1 = arena.eq(sum_sq, four).unwrap();
    let xy = arena.real_mul(xv, yv).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a2 = arena.eq(xy, one).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x²+y²=4 ∧ x*y=1 is sat with nested-radical coords; got {r:?}");
    };
    // The witnesses are genuinely algebraic (irrational), the roots of x⁴−4x²+1.
    let x = model.get(xs).expect("model must bind x");
    let y = model.get(ys).expect("model must bind y");
    let ax = x.as_real_algebraic().expect("x witness is irrational");
    let ay = y.as_real_algebraic().expect("y witness is irrational");
    assert_eq!(
        ax.sign_at(&[1, 0, -4, 0, 1]),
        Some(Sign::Zero),
        "x ∈ roots(x⁴−4x²+1)"
    );
    assert_eq!(
        ay.sign_at(&[1, 0, -4, 0, 1]),
        Some(Sign::Zero),
        "y ∈ roots(x⁴−4x²+1)"
    );
    // INDEPENDENT replay: evaluate BOTH original assertions at the model through the
    // IR ground evaluator (exact algebraic field arithmetic), expecting `true`.
    let asg = model.to_assignment();
    assert!(
        matches!(eval(&arena, a1, &asg), Ok(Value::Bool(true))),
        "x²+y²=4 must replay true at the witness"
    );
    assert!(
        matches!(eval(&arena, a2, &asg), Ok(Value::Bool(true))),
        "x·y=1 must replay true at the witness"
    );
}

/// An integer (non-Real) square is the NIA case, not ours: the real decider must
/// not fire. `int x*x = 2` is Unsat (handled by `nia_square`), and the answer must
/// still be correct — confirming we did not break the integer path.
#[test]
fn integer_square_still_unsat_via_nia() {
    let mut arena = TermArena::new();
    let xs = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(xs);
    let xx = arena.int_mul(xv, xv).unwrap();
    let two = arena.int_const(2);
    let a = arena.eq(xx, two).unwrap();
    let r = solve(&mut arena, &[a], &SolverConfig::default()).expect("no error");
    assert!(
        matches!(r, CheckResult::Unsat),
        "int x*x = 2 must stay Unsat; got {r:?}"
    );
}

#[test]
fn binomial_square_identity_proves_unsat_fast() {
    // (x+y)² = x²+2xy+y² is a TRUE polynomial identity; its negation reduces to the
    // ZERO polynomial ≠ 0, i.e. 0 ≠ 0 — recognized as UNSAT (the identity is proved),
    // instantly, not via the abstraction search. Mirrors z3's complete-NRA 0.4ms.
    let mut arena = TermArena::new();
    let (_xs, x) = real(&mut arena, "x");
    let (_ys, y) = real(&mut arena, "y");
    let xpy = arena.real_add(x, y).unwrap();
    let lhs = arena.real_mul(xpy, xpy).unwrap();
    let xx = arena.real_mul(x, x).unwrap();
    let yy = arena.real_mul(y, y).unwrap();
    let xy = arena.real_mul(x, y).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let twoxy = arena.real_mul(two, xy).unwrap();
    let s1 = arena.real_add(xx, twoxy).unwrap();
    let rhs = arena.real_add(s1, yy).unwrap();
    let neg = ne(&mut arena, lhs, rhs);
    let start = std::time::Instant::now();
    let result = solve(&mut arena, &[neg], &SolverConfig::default()).expect("solve must not error");
    assert!(
        start.elapsed() < std::time::Duration::from_secs(2),
        "must be instant, not the old 20s"
    );
    assert_eq!(
        result,
        CheckResult::Unsat,
        "the polynomial identity must be proved (Unsat), not Unknown/Sat"
    );
}

/// A single-variable goal refutation that arrives NEGATED: the valid goal
/// `x*x ≥ 0` refuted as `¬(x*x ≥ 0)` = `x*x < 0`. The collector dualizes
/// `¬(a ≥ b)` to `a < b`, so the strict atom reaches the exact single-variable
/// decider (no real root of `x²` makes it negative) and decides Unsat — mirroring
/// the multivariate negation-dualization.
#[test]
fn negated_single_var_ge_refutation_is_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let xx = arena.real_mul(xv, xv).unwrap();
    let zero = arena.real_const(Rational::zero());
    let ge = arena.real_ge(xx, zero).unwrap();
    let neg = arena.not(ge).unwrap();
    let r = solve(&mut arena, &[neg], &SolverConfig::default()).expect("no error");
    assert!(
        matches!(r, CheckResult::Unsat),
        "¬(x² ≥ 0) = x² < 0 is unsatisfiable; got {r:?}"
    );
}

// --- ALL-STRICT-inequality 2-variable CAD slice (CAD/nlsat step 3) ------------

/// Strict-inequality SAT inside the open disk: `x²+y² < 4 ∧ x > 0 ∧ y > 0`. The
/// solution set is the open quarter-disk; the CAD samples one rational interior
/// point per open x-cell and finds a satisfying y-system. The witness must be
/// rational (open cells ⇒ rational interior samples) and REPLAY against ALL three
/// original assertions through the independent ground evaluator.
#[test]
fn strict_cad_open_quarter_disk_sat() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let (ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let yy = arena.real_mul(yv, yv).unwrap();
    let sum_sq = arena.real_add(xx, yy).unwrap();
    let four = arena.real_const(Rational::integer(4));
    let a1 = arena.real_lt(sum_sq, four).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a2 = arena.real_gt(xv, zero).unwrap();
    let zero2 = arena.real_const(Rational::zero());
    let a3 = arena.real_gt(yv, zero2).unwrap();
    let r = solve(&mut arena, &[a1, a2, a3], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x²+y²<4 ∧ x>0 ∧ y>0 must be Sat (open quarter-disk); got {r:?}");
    };
    // Witness is rational (interior of an open cell).
    assert!(
        matches!(model.get(xs), Some(Value::Real(_))),
        "x witness must be rational"
    );
    assert!(
        matches!(model.get(ys), Some(Value::Real(_))),
        "y witness must be rational"
    );
    // Independent replay: ALL three original assertions hold.
    let asg = model.to_assignment();
    for (a, name) in [(a1, "x²+y²<4"), (a2, "x>0"), (a3, "y>0")] {
        assert!(
            matches!(eval(&arena, a, &asg), Ok(Value::Bool(true))),
            "{name} must replay true at the strict-CAD witness"
        );
    }
}

/// A NONCONVEX strict-inequality SAT region: `x*y > 1 ∧ y < x` (the part of the
/// hyperbola branch above 1 that lies below the diagonal — a genuinely curved,
/// non-half-plane open region; e.g. (3, 1) since 3>1 and 1<3). The CAD must find
/// a rational witness, and it replays against both assertions.
#[test]
fn strict_cad_nonconvex_hyperbola_region_sat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xy = arena.real_mul(xv, yv).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.real_gt(xy, one).unwrap();
    let a2 = arena.real_lt(yv, xv).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x*y>1 ∧ y<x must be Sat (e.g. (3,1)); got {r:?}");
    };
    let asg = model.to_assignment();
    assert!(
        matches!(eval(&arena, a1, &asg), Ok(Value::Bool(true))),
        "x*y>1 must replay true"
    );
    assert!(
        matches!(eval(&arena, a2, &asg), Ok(Value::Bool(true))),
        "y<x must replay true"
    );
}

/// Strict-inequality UNSAT (the completeness payoff): a disjoint system the outer
/// McCormick/SOS layer leaves Unknown — `x²+y² < 1 ∧ x > 2`. The open disk lives
/// in `|x| < 1`, disjoint from `x > 2`, so there is NO solution. The CAD certifies
/// **Unsat** (every open x-cell's y-system is empty), NOT Unknown.
#[test]
fn strict_cad_disjoint_disk_halfplane_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let yy = arena.real_mul(yv, yv).unwrap();
    let sum_sq = arena.real_add(xx, yy).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.real_lt(sum_sq, one).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a2 = arena.real_gt(xv, two).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        matches!(r, CheckResult::Unsat),
        "x²+y²<1 ∧ x>2 is unsat (disk inside |x|<1, disjoint from x>2); \
         the strict CAD must CERTIFY Unsat, not Unknown; got {r:?}"
    );
}

/// A coupled, genuinely nonconvex strict UNSAT: `x*y > 1 ∧ x*y < 0`. No point can
/// have its product both above 1 and below 0; the CAD certifies **Unsat** (each
/// open x-cell's y-system — `x*y>1 ∧ x*y<0` after fixing x — is empty). This is a
/// coupled (product) shape, not a single sign-definite quadratic form.
#[test]
fn strict_cad_contradictory_product_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xy = arena.real_mul(xv, yv).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.real_gt(xy, one).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a2 = arena.real_lt(xy, zero).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        matches!(r, CheckResult::Unsat),
        "x*y>1 ∧ x*y<0 is unsat (a product cannot be both >1 and <0); got {r:?}"
    );
}

/// Out-of-scope: a 2-variable component containing an EQUALITY (`x*y = 1 ∧ y < x`)
/// is NOT routed to the strict CAD. It must still decide soundly via the existing
/// equality/resultant path — and crucially must NOT be wrongly Unsat (it is sat,
/// e.g. (2, 1/2): 2·½=1 and ½<2). Confirms no behavior change for non-strict
/// components.
#[test]
fn strict_cad_equality_component_out_of_scope_not_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xy = arena.real_mul(xv, yv).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.eq(xy, one).unwrap();
    let a2 = arena.real_lt(yv, xv).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x*y=1 ∧ y<x is sat (e.g. (2,½)); a component with an equality is out of \
         strict-CAD scope and must NOT be wrongly Unsat; got {r:?}"
    );
}

/// Soundness-negative (SAT must never become Unsat): a strict system whose
/// solution set is a thin curved sliver — `x²+y² < 4 ∧ x²+y² > 3` (the open
/// annulus between radii √3 and 2). It is satisfiable (e.g. (1.9, 0) since
/// 3.61∈(3,4)). The CAD must return Sat (or at worst Unknown), NEVER Unsat.
#[test]
fn strict_cad_thin_annulus_sat_never_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let yy = arena.real_mul(yv, yv).unwrap();
    let sum_sq = arena.real_add(xx, yy).unwrap();
    let four = arena.real_const(Rational::integer(4));
    let a1 = arena.real_lt(sum_sq, four).unwrap();
    let three = arena.real_const(Rational::integer(3));
    let a2 = arena.real_gt(sum_sq, three).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Unsat),
        "the open annulus 3<x²+y²<4 is sat (e.g. (1.9,0)); must NEVER be Unsat; got {r:?}"
    );
    // If decided, the witness must genuinely replay (no wrong Sat either).
    if let CheckResult::Sat(model) = &r {
        let asg = model.to_assignment();
        assert!(
            matches!(eval(&arena, a1, &asg), Ok(Value::Bool(true)))
                && matches!(eval(&arena, a2, &asg), Ok(Value::Bool(true))),
            "any Sat witness must replay both annulus bounds true"
        );
    }
}

/// Soundness-negative (UNSAT must never become Sat): `x²+y² < 1 ∧ x²+y² > 4` is
/// unsatisfiable (a point cannot be inside radius 1 and outside radius 2). The CAD
/// must return Unsat (or Unknown), NEVER Sat. Combined with the disjoint-disk test
/// this pins both directions.
#[test]
fn strict_cad_contradictory_radii_never_sat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let yy = arena.real_mul(yv, yv).unwrap();
    let sum_sq = arena.real_add(xx, yy).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.real_lt(sum_sq, one).unwrap();
    let four = arena.real_const(Rational::integer(4));
    let a2 = arena.real_gt(sum_sq, four).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Sat(_)),
        "x²+y²<1 ∧ x²+y²>4 is unsat; must NEVER be Sat; got {r:?}"
    );
}

/// A `≠` strict atom participates in the CAD: `x²+y² < 4 ∧ x ≠ 0 ∧ y ≠ 0` is sat
/// (the punctured open disk minus the axes; e.g. (1,1)). Confirms `Ne` is handled
/// as a strict (open) atom and the witness replays.
#[test]
fn strict_cad_with_ne_atoms_sat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let yy = arena.real_mul(yv, yv).unwrap();
    let sum_sq = arena.real_add(xx, yy).unwrap();
    let four = arena.real_const(Rational::integer(4));
    let a1 = arena.real_lt(sum_sq, four).unwrap();
    let zx = arena.real_const(Rational::zero());
    let a2 = ne(&mut arena, xv, zx);
    let zy = arena.real_const(Rational::zero());
    let a3 = ne(&mut arena, yv, zy);
    let r = solve(&mut arena, &[a1, a2, a3], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x²+y²<4 ∧ x≠0 ∧ y≠0 is sat (e.g. (1,1)); got {r:?}"
    );
    if let CheckResult::Sat(model) = &r {
        let asg = model.to_assignment();
        for (a, name) in [(a1, "x²+y²<4"), (a2, "x≠0"), (a3, "y≠0")] {
            assert!(
                matches!(eval(&arena, a, &asg), Ok(Value::Bool(true))),
                "{name} must replay true"
            );
        }
    }
}

// --- Recursive N-variable (N ≥ 3) ALL-STRICT CAD slice (CAD/nlsat step 4) ------

/// Build the squared term `v*v`.
fn sq(arena: &mut TermArena, v: TermId) -> TermId {
    arena.real_mul(v, v).unwrap()
}

/// 3-variable strict SAT: `x²+y²+z² < 9 ∧ x > 0 ∧ y > 0 ∧ z > 0` — the open
/// positive octant of the open ball of radius 3. Satisfiable (e.g. (1,1,1) since
/// 3 < 9). The recursive CAD samples one rational interior point per open cell at
/// every recursion level (z eliminated, then y, then x), yields a fully RATIONAL
/// witness, and that witness REPLAYS against ALL FOUR original assertions through
/// the independent ground evaluator.
#[test]
fn strict_cad3_open_octant_ball_sat() {
    let mut arena = TermArena::new();
    let (xs, xv) = real(&mut arena, "x");
    let (ys, yv) = real(&mut arena, "y");
    let (zs, zv) = real(&mut arena, "z");
    let xx = sq(&mut arena, xv);
    let yy = sq(&mut arena, yv);
    let zz = sq(&mut arena, zv);
    let s1 = arena.real_add(xx, yy).unwrap();
    let sum_sq = arena.real_add(s1, zz).unwrap();
    let nine = arena.real_const(Rational::integer(9));
    let a1 = arena.real_lt(sum_sq, nine).unwrap();
    let z0 = arena.real_const(Rational::zero());
    let a2 = arena.real_gt(xv, z0).unwrap();
    let z1 = arena.real_const(Rational::zero());
    let a3 = arena.real_gt(yv, z1).unwrap();
    let z2 = arena.real_const(Rational::zero());
    let a4 = arena.real_gt(zv, z2).unwrap();
    let r = solve(&mut arena, &[a1, a2, a3, a4], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("x²+y²+z²<9 ∧ x,y,z>0 must be Sat (open octant ball); got {r:?}");
    };
    // Witness must be fully rational (open cells ⇒ rational interior samples).
    for (sym, name) in [(xs, "x"), (ys, "y"), (zs, "z")] {
        assert!(
            matches!(model.get(sym), Some(Value::Real(_))),
            "{name} witness must be rational"
        );
    }
    // Independent replay: ALL FOUR original assertions hold at the witness.
    let asg = model.to_assignment();
    for (a, name) in [(a1, "x²+y²+z²<9"), (a2, "x>0"), (a3, "y>0"), (a4, "z>0")] {
        assert!(
            matches!(eval(&arena, a, &asg), Ok(Value::Bool(true))),
            "{name} must replay true at the 3-var strict-CAD witness"
        );
    }
}

/// 3-variable strict UNSAT (the completeness payoff): `x²+y²+z² < 1 ∧ x > 2`. The
/// open ball lives in `|x| < 1`, disjoint from `x > 2` ⇒ NO solution. The recursive
/// CAD certifies **Unsat** (every open cell's fiber system is empty), not Unknown.
#[test]
fn strict_cad3_disjoint_ball_halfspace_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let (_zs, zv) = real(&mut arena, "z");
    let xx = sq(&mut arena, xv);
    let yy = sq(&mut arena, yv);
    let zz = sq(&mut arena, zv);
    let s1 = arena.real_add(xx, yy).unwrap();
    let sum_sq = arena.real_add(s1, zz).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.real_lt(sum_sq, one).unwrap();
    let two = arena.real_const(Rational::integer(2));
    let a2 = arena.real_gt(xv, two).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        matches!(r, CheckResult::Unsat),
        "x²+y²+z²<1 ∧ x>2 is unsat (ball inside |x|<1, disjoint from x>2); the \
         recursive strict CAD must CERTIFY Unsat, not Unknown; got {r:?}"
    );
}

/// Soundness-negative (SAT must NEVER become Unsat): a 3-var CURVED open region —
/// a spherical cap `x²+y²+z² < 4 ∧ x > 1` (inside radius 2, beyond the plane x=1).
/// Satisfiable (e.g. (1.5,0,0): 2.25 < 4 and 1.5 > 1). The boundary is a genuine
/// sphere (not a half-space), so the CAD must sample a curved fiber. Must be Sat or
/// Unknown — NEVER Unsat — and any Sat witness must genuinely replay both atoms.
#[test]
fn strict_cad3_spherical_cap_sat_never_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let (_zs, zv) = real(&mut arena, "z");
    let xx = sq(&mut arena, xv);
    let yy = sq(&mut arena, yv);
    let zz = sq(&mut arena, zv);
    let s1 = arena.real_add(xx, yy).unwrap();
    let sum_sq = arena.real_add(s1, zz).unwrap();
    let four = arena.real_const(Rational::integer(4));
    let a1 = arena.real_lt(sum_sq, four).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a2 = arena.real_gt(xv, one).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Unsat),
        "the open cap x²+y²+z²<4 ∧ x>1 is sat (e.g. (1.5,0,0)); must NEVER be Unsat; got {r:?}"
    );
    if let CheckResult::Sat(model) = &r {
        let asg = model.to_assignment();
        assert!(
            matches!(eval(&arena, a1, &asg), Ok(Value::Bool(true)))
                && matches!(eval(&arena, a2, &asg), Ok(Value::Bool(true))),
            "any Sat witness must replay both cap bounds true"
        );
    }
}

/// Soundness-negative (UNSAT must NEVER become Sat): `x²+y²+z² < 1 ∧ x²+y²+z² > 4`
/// is unsatisfiable (a point cannot be inside radius 1 and outside radius 2). Must
/// be Unsat or Unknown — NEVER Sat.
#[test]
fn strict_cad3_contradictory_radii_never_sat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let (_zs, zv) = real(&mut arena, "z");
    let xx = sq(&mut arena, xv);
    let yy = sq(&mut arena, yv);
    let zz = sq(&mut arena, zv);
    let s1 = arena.real_add(xx, yy).unwrap();
    let sum_sq = arena.real_add(s1, zz).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.real_lt(sum_sq, one).unwrap();
    let four = arena.real_const(Rational::integer(4));
    let a2 = arena.real_gt(sum_sq, four).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Sat(_)),
        "x²+y²+z²<1 ∧ x²+y²+z²>4 is unsat; must NEVER be Sat; got {r:?}"
    );
}

/// A coupled 3-var strict UNSAT via a product sign contradiction: `x*y*z > 1 ∧
/// x*y*z < 0`. No point's triple product is both above 1 and below 0. The recursive
/// CAD must certify Unsat, NEVER Sat (and never hang).
#[test]
fn strict_cad3_contradictory_triple_product_never_sat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let (_zs, zv) = real(&mut arena, "z");
    let xy = arena.real_mul(xv, yv).unwrap();
    let xyz = arena.real_mul(xy, zv).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.real_gt(xyz, one).unwrap();
    let zero = arena.real_const(Rational::zero());
    let a2 = arena.real_lt(xyz, zero).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Sat(_)),
        "x*y*z>1 ∧ x*y*z<0 is unsat (a product cannot be both >1 and <0); \
         must NEVER be Sat; got {r:?}"
    );
}

/// Out-of-scope: a ≥3-var component containing an EQUALITY (`x*y*z = 1 ∧ x > 0 ∧
/// y > 0`) is NOT routed to the recursive strict CAD. It must NOT be wrongly Unsat
/// (it is sat, e.g. (1,1,1)); a sound decline (Unknown) is acceptable.
#[test]
fn strict_cad3_equality_component_out_of_scope_not_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let (_zs, zv) = real(&mut arena, "z");
    let xy = arena.real_mul(xv, yv).unwrap();
    let xyz = arena.real_mul(xy, zv).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.eq(xyz, one).unwrap();
    let z0 = arena.real_const(Rational::zero());
    let a2 = arena.real_gt(xv, z0).unwrap();
    let z1 = arena.real_const(Rational::zero());
    let a3 = arena.real_gt(yv, z1).unwrap();
    let r = solve(&mut arena, &[a1, a2, a3], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x*y*z=1 ∧ x>0 ∧ y>0 is sat (e.g. (1,1,1)); a ≥3-var component with an \
         equality is out of strict-CAD scope and must NOT be wrongly Unsat; got {r:?}"
    );
}

/// `≠` atoms participate in the recursive CAD: `x²+y²+z² < 9 ∧ x ≠ 0 ∧ y ≠ 0 ∧
/// z ≠ 0` (the punctured open ball minus the coordinate planes; e.g. (1,1,1)). Must
/// not be Unsat; any Sat witness replays.
#[test]
fn strict_cad3_with_ne_atoms_sat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let (_zs, zv) = real(&mut arena, "z");
    let xx = sq(&mut arena, xv);
    let yy = sq(&mut arena, yv);
    let zz = sq(&mut arena, zv);
    let s1 = arena.real_add(xx, yy).unwrap();
    let sum_sq = arena.real_add(s1, zz).unwrap();
    let nine = arena.real_const(Rational::integer(9));
    let a1 = arena.real_lt(sum_sq, nine).unwrap();
    let zx = arena.real_const(Rational::zero());
    let a2 = ne(&mut arena, xv, zx);
    let zy = arena.real_const(Rational::zero());
    let a3 = ne(&mut arena, yv, zy);
    let zz0 = arena.real_const(Rational::zero());
    let a4 = ne(&mut arena, zv, zz0);
    let r = solve(&mut arena, &[a1, a2, a3, a4], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x²+y²+z²<9 ∧ x≠0 ∧ y≠0 ∧ z≠0 is sat (e.g. (1,1,1)); got {r:?}"
    );
    if let CheckResult::Sat(model) = &r {
        let asg = model.to_assignment();
        for (a, name) in [(a1, "x²+y²+z²<9"), (a2, "x≠0"), (a3, "y≠0"), (a4, "z≠0")] {
            assert!(
                matches!(eval(&arena, a, &asg), Ok(Value::Bool(true))),
                "{name} must replay true"
            );
        }
    }
}

/// Bounded: a high-degree, many-variable strict input must DECLINE (or decide)
/// WITHOUT hanging / OOM / panicking — the cell-count / Sylvester caps guard the
/// combinatorial blow-up. `x⁴+y⁴+z⁴+w⁴ < 1 ∧ x>0 ∧ y>0 ∧ z>0 ∧ w>0` (4 vars,
/// degree 4). Whatever the verdict, it must be sound: if Sat, it replays; it must
/// never be a wrong Unsat (the region is nonempty, e.g. near the origin).
#[test]
fn strict_cad_high_degree_many_var_bounded_no_hang() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let (_zs, zv) = real(&mut arena, "z");
    let (_ws, wv) = real(&mut arena, "w");
    let quart = |arena: &mut TermArena, v: TermId| {
        let v2 = arena.real_mul(v, v).unwrap();
        arena.real_mul(v2, v2).unwrap()
    };
    let x4 = quart(&mut arena, xv);
    let y4 = quart(&mut arena, yv);
    let z4 = quart(&mut arena, zv);
    let w4 = quart(&mut arena, wv);
    let s1 = arena.real_add(x4, y4).unwrap();
    let s2 = arena.real_add(s1, z4).unwrap();
    let sum = arena.real_add(s2, w4).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.real_lt(sum, one).unwrap();
    let z0 = arena.real_const(Rational::zero());
    let a2 = arena.real_gt(xv, z0).unwrap();
    let z1 = arena.real_const(Rational::zero());
    let a3 = arena.real_gt(yv, z1).unwrap();
    let z2 = arena.real_const(Rational::zero());
    let a4 = arena.real_gt(zv, z2).unwrap();
    let z3 = arena.real_const(Rational::zero());
    let a5 = arena.real_gt(wv, z3).unwrap();
    let r =
        solve(&mut arena, &[a1, a2, a3, a4, a5], &SolverConfig::default()).expect("no error/hang");
    // Soundness: the region is nonempty (e.g. (0.5,0.5,0.5,0.5): 4·0.0625=0.25<1),
    // so it must NEVER be Unsat. Sat (replayed) or Unknown are both acceptable.
    assert!(
        !matches!(r, CheckResult::Unsat),
        "the open region x⁴+y⁴+z⁴+w⁴<1 ∧ x,y,z,w>0 is nonempty; must NEVER be Unsat; got {r:?}"
    );
    if let CheckResult::Sat(model) = &r {
        let asg = model.to_assignment();
        for a in [a1, a2, a3, a4, a5] {
            assert!(
                matches!(eval(&arena, a, &asg), Ok(Value::Bool(true))),
                "any Sat witness must replay every atom true"
            );
        }
    }
}

/// Second fuzz-found WRONG-UNSAT (seed 1924): a single-variable strict system
/// `2 + 3z² > 0 ∧ 3 − 3z² + z < 0` (clearly Sat — atom0 is always true, atom1
/// holds for z ≤ −1) was reported `Unsat`. Root cause: `cell_samples` derived its
/// per-cell witnesses from `Root::locate` (a depth-48 isolating-interval dyadic),
/// so for atom1's IRRATIONAL roots `(1 ± √37)/6` the samples had ~2⁴⁹
/// denominators; evaluating the original term there OVERFLOWED `i128`, the replay
/// gate read the `Err` as "witness invalid", and with every valid witness rejected
/// `decide_system` concluded `Unsat`. Fix: `cell_samples` now picks SIMPLE
/// in-cell rationals (integers / coarse dyadics from the safe gap between roots),
/// and the replay distinguishes overflow (`None` ⇒ decline) from a genuine `false`
/// — so a witness is never silently dropped into a wrong `Unsat`. The witness here
/// is now the clean integer `z = −2`.
#[test]
fn strict_single_var_wrong_unsat_regression_seed_1924_is_sat() {
    let mut a = TermArena::new();
    let (zs, z) = real(&mut a, "z");
    let zz = a.real_mul(z, z).unwrap();
    let three = a.real_const(Rational::integer(3));
    let t3zz = a.real_mul(three, zz).unwrap();
    let two = a.real_const(Rational::integer(2));
    let p0 = a.real_add(two, t3zz).unwrap();
    let zero = a.real_const(Rational::zero());
    let atom0 = a.real_gt(p0, zero).unwrap(); // 2 + 3z² > 0
    let m3 = a.real_const(Rational::integer(-3));
    let m3zz = a.real_mul(m3, zz).unwrap();
    let three2 = a.real_const(Rational::integer(3));
    let sum = a.real_add(three2, m3zz).unwrap();
    let p1 = a.real_add(sum, z).unwrap();
    let zero2 = a.real_const(Rational::zero());
    let atom1 = a.real_lt(p1, zero2).unwrap(); // 3 − 3z² + z < 0

    let r = solve(&mut a, &[atom0, atom1], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("2+3z²>0 ∧ 3-3z²+z<0 is SAT (e.g. z=-2); got {r:?}");
    };
    assert!(
        matches!(model.get(zs), Some(Value::Real(_))),
        "witness must be a (clean) rational"
    );
    let asg = model.to_assignment();
    for (t, n) in [(atom0, "2+3z²>0"), (atom1, "3-3z²+z<0")] {
        assert!(
            matches!(eval(&a, t, &asg), Ok(Value::Bool(true))),
            "{n} must replay true at the witness (no eval overflow)"
        );
    }
}

/// Regression for the fuzz-found WRONG-UNSAT (the adversarial Z3 differential
/// harness, seed 1117, minimized): `3xy + 3 + 3x < 0 ∧ xy > 0` is satisfiable
/// (witness x = −2, y = −1/4: A = −3/2 < 0, B = 1/2 > 0), yet the strict-CAD path
/// reported `Unsat`. Root cause was in `sturm_isolate_rec`: splitting the Cauchy
/// interval at a midpoint that is ITSELF a root (here x = 0, the midpoint of the
/// symmetric `[−B, B]`, a root of the pairwise resultant `−3x²−3x`) recorded the
/// midpoint and then recursed on the left half with a count that excluded it,
/// causing the `count == 1` leaf to grab the midpoint AGAIN (`eval(hi) == 0`) and
/// MISS the genuine left root `x = −1`. So `isolate_roots(−3x²−3x)` returned
/// `{0, 0}` instead of `{−1, 0}`, the CAD missed the open cell `(−∞, −1)` holding
/// the witness, and every sampled cell was (correctly, but incompletely) Unsat.
/// The fix makes the half-open split `(lo, mid] + (mid, hi]` unconditional (it
/// always partitions exactly, root-at-mid or not), so the root at `mid` is found
/// once by the left half. This is a foundational root-isolation fix — it affects
/// every NRA decider, not just the CAD.
#[test]
fn strict_cad_wrong_unsat_regression_seed_1117_is_sat() {
    let mut a = TermArena::new();
    let (xs, x) = real(&mut a, "x");
    let (ys, y) = real(&mut a, "y");
    let xy = a.real_mul(x, y).unwrap();
    let three = a.real_const(Rational::integer(3));
    let three_xy = a.real_mul(three, xy).unwrap();
    let three_c = a.real_const(Rational::integer(3));
    let three_x = a.real_mul(three_c, x).unwrap();
    let c3 = a.real_const(Rational::integer(3));
    let s1 = a.real_add(three_xy, c3).unwrap();
    let a_poly = a.real_add(s1, three_x).unwrap();
    let zero = a.real_const(Rational::zero());
    let atom_a = a.real_lt(a_poly, zero).unwrap(); // 3xy + 3 + 3x < 0
    let xy2 = a.real_mul(x, y).unwrap();
    let zero2 = a.real_const(Rational::zero());
    let atom_b = a.real_gt(xy2, zero2).unwrap(); // xy > 0

    let r = solve(&mut a, &[atom_a, atom_b], &SolverConfig::default()).expect("no error");
    let CheckResult::Sat(model) = &r else {
        panic!("3xy+3+3x<0 ∧ xy>0 is SAT (x=-2, y=-1/4); got {r:?}");
    };
    // The witnesses are rational (interior of an open cell).
    assert!(matches!(model.get(xs), Some(Value::Real(_))));
    assert!(matches!(model.get(ys), Some(Value::Real(_))));
    // Independent replay: both original atoms hold at the returned model.
    let asg = model.to_assignment();
    for (t, n) in [(atom_a, "3xy+3+3x<0"), (atom_b, "xy>0")] {
        assert!(
            matches!(eval(&a, t, &asg), Ok(Value::Bool(true))),
            "{n} must replay true at the witness"
        );
    }
}
