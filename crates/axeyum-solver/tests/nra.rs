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
fn product_forcing_contradiction_with_linear_is_sat_or_unsat_soundly() {
    // x*y == 6 AND x == 2 AND y == 4: replay gives 2*4=8 != 6 -> the candidate
    // fails, so the sound answer is unknown (not a wrong sat/unsat).
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
    // 2*4=8 ≠ 6 so this is actually unsat; the abstraction can't see that, so a
    // sound solver returns unknown here (never a wrong sat).
    assert!(
        matches!(r, CheckResult::Unknown(_) | CheckResult::Unsat),
        "must not be a wrong sat; got {r:?}"
    );
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
