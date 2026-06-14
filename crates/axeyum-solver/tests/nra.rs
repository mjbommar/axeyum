//! Nonlinear real arithmetic via linear abstraction + replay (sound, incomplete).
#![allow(clippy::many_single_char_names)]

use axeyum_ir::{Rational, Sort, TermArena};
use axeyum_solver::{CheckResult, SolverConfig, check_with_nra};

fn real(arena: &mut TermArena, name: &str) -> axeyum_ir::TermId {
    let s = arena.declare(name, Sort::Real).unwrap();
    arena.var(s)
}

#[test]
fn same_product_two_values_is_unsat() {
    // x*y == 5 AND x*y == 6: the same nonlinear product can't be both — the
    // abstraction maps it to one variable, so LRA proves unsat soundly.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let p = a.real_mul(x, y).unwrap();
    let five = a.real_const(Rational::integer(5));
    let six = a.real_const(Rational::integer(6));
    let e5 = a.eq(p, five).unwrap();
    let p2 = a.real_mul(x, y).unwrap();
    let e6 = a.eq(p2, six).unwrap();

    let r = check_with_nra(&mut a, &[e5, e6], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Unsat), "x*y=5 ∧ x*y=6 must be unsat, got {r:?}");
}

#[test]
fn constrained_product_is_sat_via_replay() {
    // x*y == 6 AND x == 2 AND y == 3: the linear part pins x,y, so the replayed
    // candidate satisfies the true product -> sat.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let p = a.real_mul(x, y).unwrap();
    let six = a.real_const(Rational::integer(6));
    let two = a.real_const(Rational::integer(2));
    let three = a.real_const(Rational::integer(3));
    let e6 = a.eq(p, six).unwrap();
    let ex = a.eq(x, two).unwrap();
    let ey = a.eq(y, three).unwrap();

    let r = check_with_nra(&mut a, &[e6, ex, ey], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Sat(_)), "2*3=6 must be sat, got {r:?}");
}

#[test]
fn refinement_decides_inconsistent_pinned_product() {
    // x*y == 6 AND x == 2 AND y == 4: 2*4=8 ≠ 6, so unsat. The point-lemma
    // refinement loop (add (x=2 ∧ y=4)→r=8 on replay failure) decides it.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let p = a.real_mul(x, y).unwrap();
    let six = a.real_const(Rational::integer(6));
    let two = a.real_const(Rational::integer(2));
    let four = a.real_const(Rational::integer(4));
    let e6 = a.eq(p, six).unwrap();
    let ex = a.eq(x, two).unwrap();
    let ey = a.eq(y, four).unwrap();

    let r = check_with_nra(&mut a, &[e6, ex, ey], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Unsat), "2*4=8≠6 must be unsat, got {r:?}");
}

#[test]
fn square_is_nonnegative_so_negative_square_is_unsat() {
    // x*x < 0 is unsat (x^2 >= 0) — decided by the sign lemma, not nonlinear
    // reasoning: (x>=0 ∧ x>=0)→r>=0 and (x<=0 ∧ x<=0)→r>=0, and x>=0 ∨ x<=0.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let sq = a.real_mul(x, x).unwrap();
    let zero = a.real_const(Rational::integer(0));
    let neg = a.real_lt(sq, zero).unwrap(); // x*x < 0
    let r = check_with_nra(&mut a, &[neg], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Unsat), "x*x < 0 must be unsat, got {r:?}");
}

#[test]
fn sign_rule_decides_product_of_positives() {
    // x > 0 ∧ y > 0 ∧ x*y < 0 is unsat by the sign rule.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let zero = a.real_const(Rational::integer(0));
    let xpos = a.real_gt(x, zero).unwrap();
    let ypos = a.real_gt(y, zero).unwrap();
    let p = a.real_mul(x, y).unwrap();
    let pneg = a.real_lt(p, zero).unwrap();
    let r = check_with_nra(&mut a, &[xpos, ypos, pneg], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Unsat), "pos*pos<0 must be unsat, got {r:?}");
}

#[test]
fn zero_rule_decides() {
    // x == 0 ∧ x*y == 5 is unsat (x=0 ⇒ x*y=0 ≠ 5) by the zero rule.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let zero = a.real_const(Rational::integer(0));
    let five = a.real_const(Rational::integer(5));
    let xz = a.eq(x, zero).unwrap();
    let p = a.real_mul(x, y).unwrap();
    let p5 = a.eq(p, five).unwrap();
    let r = check_with_nra(&mut a, &[xz, p5], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Unsat), "x=0 ∧ x*y=5 must be unsat, got {r:?}");
}

#[test]
fn linear_real_still_works_through_nra() {
    // No nonlinear products -> delegates straight to LRA. x + 1 == 3 -> sat.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let one = a.real_const(Rational::integer(1));
    let three = a.real_const(Rational::integer(3));
    let sum = a.real_add(x, one).unwrap();
    let eq = a.eq(sum, three).unwrap();
    let r = check_with_nra(&mut a, &[eq], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Sat(_)), "x+1=3 sat, got {r:?}");
}

#[test]
fn mccormick_bounds_product_above_max_is_unsat() {
    // 0<=x<=2 ∧ 0<=y<=2 ∧ x*y > 4: the product cannot exceed 4 on [0,2]^2.
    // The McCormick envelopes (r <= 2y, r <= 2x) bound it; sign rules cannot.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let zero = a.real_const(Rational::integer(0));
    let two = a.real_const(Rational::integer(2));
    let four = a.real_const(Rational::integer(4));
    let xl = a.real_ge(x, zero).unwrap();
    let xu = a.real_le(x, two).unwrap();
    let yl = a.real_ge(y, zero).unwrap();
    let yu = a.real_le(y, two).unwrap();
    let p = a.real_mul(x, y).unwrap();
    let big = a.real_gt(p, four).unwrap();
    let r = check_with_nra(&mut a, &[xl, xu, yl, yu, big], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Unsat), "x*y>4 on [0,2]^2 must be unsat, got {r:?}");
}

#[test]
fn mccormick_square_above_secant_is_unsat() {
    // 0<=x<=2 ∧ x*x > 2x: on [0,2], x^2 <= 2x (since x(x-2)<=0). The upper
    // McCormick envelope of x^2 on [0,2] is exactly r <= 2x, contradicting r>2x.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let zero = a.real_const(Rational::integer(0));
    let two = a.real_const(Rational::integer(2));
    let xl = a.real_ge(x, zero).unwrap();
    let xu = a.real_le(x, two).unwrap();
    let sq = a.real_mul(x, x).unwrap();
    let two_x = a.real_mul(two, x).unwrap(); // linear (const * term), not abstracted
    let gt = a.real_gt(sq, two_x).unwrap();
    let r = check_with_nra(&mut a, &[xl, xu, gt], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Unsat), "x^2 > 2x on [0,2] must be unsat, got {r:?}");
}

#[test]
fn mccormick_feasible_product_is_sat() {
    // 0<=x<=2 ∧ 0<=y<=2 ∧ x*y == 4: feasible (x=y=2); envelopes must not reject it.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let zero = a.real_const(Rational::integer(0));
    let two = a.real_const(Rational::integer(2));
    let four = a.real_const(Rational::integer(4));
    let xl = a.real_ge(x, zero).unwrap();
    let xu = a.real_le(x, two).unwrap();
    let yl = a.real_ge(y, zero).unwrap();
    let yu = a.real_le(y, two).unwrap();
    let p = a.real_mul(x, y).unwrap();
    let eq4 = a.eq(p, four).unwrap();
    let r = check_with_nra(&mut a, &[xl, xu, yl, yu, eq4], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Sat(_)), "x*y=4 on [0,2]^2 must be sat, got {r:?}");
}

#[test]
fn bnb_square_strict_gap_is_unsat() {
    // -5<=x<=5 ∧ x*x < 2x - 2 : x^2 - 2x + 2 = (x-1)^2 + 1 >= 1 > 0, so unsat
    // with a strict gap. The root McCormick envelope on [-5,5] is too loose;
    // spatial branch-and-bound subdivides until each subdomain refutes it.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let neg5 = a.real_const(Rational::integer(-5));
    let five = a.real_const(Rational::integer(5));
    let two = a.real_const(Rational::integer(2));
    let xl = a.real_ge(x, neg5).unwrap();
    let xu = a.real_le(x, five).unwrap();
    let sq = a.real_mul(x, x).unwrap();
    let two_x = a.real_mul(two, x).unwrap();
    let rhs = a.real_sub(two_x, two).unwrap(); // 2x - 2
    let lt = a.real_lt(sq, rhs).unwrap();
    let r = check_with_nra(&mut a, &[xl, xu, lt], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Unsat), "x^2 < 2x-2 on [-5,5] must be unsat, got {r:?}");
}

#[test]
fn bnb_two_variable_box_unsat() {
    // 1<=x<=3 ∧ 1<=y<=3 ∧ x*y > 9 : max of x*y on the box is 9, so >9 is unsat.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let one = a.real_const(Rational::integer(1));
    let three = a.real_const(Rational::integer(3));
    let nine = a.real_const(Rational::integer(9));
    let xl = a.real_ge(x, one).unwrap();
    let xu = a.real_le(x, three).unwrap();
    let yl = a.real_ge(y, one).unwrap();
    let yu = a.real_le(y, three).unwrap();
    let p = a.real_mul(x, y).unwrap();
    let gt = a.real_gt(p, nine).unwrap();
    let r = check_with_nra(&mut a, &[xl, xu, yl, yu, gt], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Unsat), "x*y>9 on [1,3]^2 must be unsat, got {r:?}");
}

#[test]
fn bnb_feasible_square_stays_sat() {
    // -5<=x<=5 ∧ x*x > 2x + 2 : feasible (e.g. x=5: 25>12). Must stay sat under B&B.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let neg5 = a.real_const(Rational::integer(-5));
    let five = a.real_const(Rational::integer(5));
    let two = a.real_const(Rational::integer(2));
    let xl = a.real_ge(x, neg5).unwrap();
    let xu = a.real_le(x, five).unwrap();
    let sq = a.real_mul(x, x).unwrap();
    let two_x = a.real_mul(two, x).unwrap();
    let rhs = a.real_add(two_x, two).unwrap(); // 2x + 2
    let gt = a.real_gt(sq, rhs).unwrap();
    let r = check_with_nra(&mut a, &[xl, xu, gt], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Sat(_)), "x^2 > 2x+2 on [-5,5] must be sat, got {r:?}");
}

#[test]
fn bnb_unbounded_square_is_unknown_not_wrong_unsat() {
    // x*x < -1 with x unbounded: truly unsat, but the sign rule already proves
    // it (x^2 >= 0). Use a case the sign rule can't: x*x < 2x - 2 with NO bounds
    // on x. Unsat in truth, but B&B cannot branch an unbounded var -> unknown
    // (never a wrong unsat, and never a wrong sat).
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let two = a.real_const(Rational::integer(2));
    let sq = a.real_mul(x, x).unwrap();
    let two_x = a.real_mul(two, x).unwrap();
    let rhs = a.real_sub(two_x, two).unwrap();
    let lt = a.real_lt(sq, rhs).unwrap();
    let r = check_with_nra(&mut a, &[lt], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Unknown(_)), "unbounded x^2<2x-2 -> unknown, got {r:?}");
}

#[test]
fn real_division_pinned_is_sat() {
    // x / y == 2 AND y == 3 AND x == 6 : sat (6/3 = 2).
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let d = a.real_div(x, y).unwrap();
    let two = a.real_const(Rational::integer(2));
    let three = a.real_const(Rational::integer(3));
    let six = a.real_const(Rational::integer(6));
    let dc = a.eq(d, two).unwrap();
    let yc = a.eq(y, three).unwrap();
    let xc = a.eq(x, six).unwrap();
    let r = check_with_nra(&mut a, &[dc, yc, xc], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Sat(_)), "6/3=2 sat, got {r:?}");
}

#[test]
fn real_division_inconsistent_is_unsat() {
    // x / y == 2 AND y == 3 AND x == 7 : unsat (7 = 2*3 = 6 is false).
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let d = a.real_div(x, y).unwrap();
    let two = a.real_const(Rational::integer(2));
    let three = a.real_const(Rational::integer(3));
    let seven = a.real_const(Rational::integer(7));
    let dc = a.eq(d, two).unwrap();
    let yc = a.eq(y, three).unwrap();
    let xc = a.eq(x, seven).unwrap();
    let r = check_with_nra(&mut a, &[dc, yc, xc], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Unsat), "7/3 != 2 unsat, got {r:?}");
}

#[test]
fn real_division_by_zero_is_unconstrained() {
    // y == 0 AND x == 5 AND x/y == 100 : sat (x/0 is unspecified, so r=100 ok).
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let d = a.real_div(x, y).unwrap();
    let zero = a.real_const(Rational::integer(0));
    let five = a.real_const(Rational::integer(5));
    let hundred = a.real_const(Rational::integer(100));
    let yc = a.eq(y, zero).unwrap();
    let xc = a.eq(x, five).unwrap();
    let dc = a.eq(d, hundred).unwrap();
    let r = check_with_nra(&mut a, &[yc, xc, dc], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Sat(_)), "x/0 unconstrained -> sat, got {r:?}");
}
