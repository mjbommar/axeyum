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
