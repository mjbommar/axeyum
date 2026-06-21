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

/// A genuinely coupled equality system with an algebraic-valued witness, decided
/// Sat and replay-checked: `x² + y² = 4 ∧ x*y = 1`. Common solutions have
/// irrational coordinates; `Res_y = x⁴ − 4x² + 1`, whose roots are irrational.
/// Because the x-candidates are algebraic (not rational), the lift DECLINES — the
/// decider must not crash and must not answer Unsat (it IS satisfiable).
#[test]
fn multi_coupled_algebraic_x_declines_not_unsat() {
    let mut arena = TermArena::new();
    let (_xs, xv) = real(&mut arena, "x");
    let (_ys, yv) = real(&mut arena, "y");
    let xx = arena.real_mul(xv, xv).unwrap();
    let yy = arena.real_mul(yv, yv).unwrap();
    let sum_sq = arena.real_add(xx, yy).unwrap();
    let four = arena.real_const(Rational::integer(4));
    let a1 = arena.eq(sum_sq, four).unwrap();
    let xy = arena.real_mul(xv, yv).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let a2 = arena.eq(xy, one).unwrap();
    let r = solve(&mut arena, &[a1, a2], &SolverConfig::default()).expect("no error");
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x²+y²=4 ∧ x*y=1 is sat (irrational coords); algebraic-x lift declines, not Unsat; got {r:?}"
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
