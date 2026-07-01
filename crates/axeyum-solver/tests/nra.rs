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
    assert!(
        matches!(r, CheckResult::Unsat),
        "x*y=5 ∧ x*y=6 must be unsat, got {r:?}"
    );
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
    assert!(
        matches!(r, CheckResult::Sat(_)),
        "2*3=6 must be sat, got {r:?}"
    );
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
    assert!(
        matches!(r, CheckResult::Unsat),
        "2*4=8≠6 must be unsat, got {r:?}"
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
    assert!(
        matches!(r, CheckResult::Unsat),
        "x*x < 0 must be unsat, got {r:?}"
    );
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
    assert!(
        matches!(r, CheckResult::Unsat),
        "pos*pos<0 must be unsat, got {r:?}"
    );
}

#[test]
fn monotonicity_rule_decides_product_of_at_least_ones() {
    // x ≥ 1 ∧ y ≥ 1 ∧ x*y < 1 is unsat: x*y ≥ y ≥ 1, which the sign/zero rules
    // miss (r ≥ 0 is consistent with r < 1) but the threshold-1 monotonicity
    // lemma (x≥1 ∧ y≥0 → x*y ≥ y) catches.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let one = a.real_const(Rational::integer(1));
    let xge = a.real_ge(x, one).unwrap();
    let yge = a.real_ge(y, one).unwrap();
    let p = a.real_mul(x, y).unwrap();
    let plt = a.real_lt(p, one).unwrap();
    let r = check_with_nra(&mut a, &[xge, yge, plt], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "x≥1 ∧ y≥1 ∧ x*y<1 must be unsat, got {r:?}"
    );
}

#[test]
fn shrinking_rule_decides_product_below_factor() {
    // 0 ≤ x ≤ 1 ∧ y ≥ 0 ∧ x*y > y is unsat: x*y ≤ 1*y = y. Only x is bounded
    // above, so the two-sided McCormick envelope cannot apply — the threshold-1
    // shrinking lemma (0≤x≤1 ∧ y≥0 → x*y ≤ y) catches it.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let zero = a.real_const(Rational::integer(0));
    let one = a.real_const(Rational::integer(1));
    let xlo = a.real_ge(x, zero).unwrap();
    let xhi = a.real_le(x, one).unwrap();
    let ylo = a.real_ge(y, zero).unwrap();
    let p = a.real_mul(x, y).unwrap();
    let pgt = a.real_gt(p, y).unwrap();
    let r = check_with_nra(&mut a, &[xlo, xhi, ylo, pgt], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "0≤x≤1 ∧ y≥0 ∧ x*y>y must be unsat, got {r:?}"
    );
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
    assert!(
        matches!(r, CheckResult::Unsat),
        "x=0 ∧ x*y=5 must be unsat, got {r:?}"
    );
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
    assert!(
        matches!(r, CheckResult::Unsat),
        "x*y>4 on [0,2]^2 must be unsat, got {r:?}"
    );
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
    assert!(
        matches!(r, CheckResult::Unsat),
        "x^2 > 2x on [0,2] must be unsat, got {r:?}"
    );
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
    assert!(
        matches!(r, CheckResult::Sat(_)),
        "x*y=4 on [0,2]^2 must be sat, got {r:?}"
    );
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
    assert!(
        matches!(r, CheckResult::Unsat),
        "x^2 < 2x-2 on [-5,5] must be unsat, got {r:?}"
    );
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
    assert!(
        matches!(r, CheckResult::Unsat),
        "x*y>9 on [1,3]^2 must be unsat, got {r:?}"
    );
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
    assert!(
        matches!(r, CheckResult::Sat(_)),
        "x^2 > 2x+2 on [-5,5] must be sat, got {r:?}"
    );
}

#[test]
fn unbounded_single_var_square_is_decided_unsat() {
    // x*x < 2x - 2 with NO bounds on x, i.e. (x-1)² + 1 < 0 — truly UNSAT (the
    // expression is ≥ 1 everywhere). The bounded B&B relaxation alone cannot branch
    // an unbounded variable and would only manage `unknown`; the exact single-
    // variable real-root decider (no real root ⇒ the strict `<0` is empty) now
    // proves it UNSAT completely. A strict improvement, and never a wrong `sat`.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let two = a.real_const(Rational::integer(2));
    let sq = a.real_mul(x, x).unwrap();
    let two_x = a.real_mul(two, x).unwrap();
    let rhs = a.real_sub(two_x, two).unwrap();
    let lt = a.real_lt(sq, rhs).unwrap();
    let r = check_with_nra(&mut a, &[lt], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "unbounded (x-1)²+1<0 is empty ⇒ unsat, got {r:?}"
    );
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
fn real_division_by_zero_is_sound_unknown() {
    // y == 0 AND x == 5 AND x/y == 100.
    //
    // This case sits on a genuine semantic divergence that the solver reconciles
    // to a *sound* `unknown` rather than a definite verdict:
    //
    //   * axeyum's ground evaluator — the trusted soundness anchor for every `sat`
    //     replay (see `axeyum-ir` `real_division_evaluates_exactly`) — COMMITS to
    //     the totality convention `x / 0 = 0` (like SMT-LIB `bvudiv x 0 = all-ones`).
    //     Under that convention `5 / 0 = 0 ≠ 100`, so the query is unsatisfiable and
    //     no model can replay it.
    //   * SMT-LIB / Z3 leave real `/0` *unspecified* (a free value), so Z3 reports
    //     `sat` (pick the division result to be 100).
    //
    // A definite `unsat` would DISAGREE with Z3 (a wrong-unsat); a `sat` cannot
    // produce a model the `/0 = 0` evaluator will accept (and the differential
    // fuzz's replay anchor would refute it). The only verdict sound under BOTH
    // commitments is `unknown`. Recovering these as real `sat`s requires
    // first-class free-division witnesses (the model carrying the chosen `x/0`
    // value so the evaluator can validate it) — a tracked NRA follow-up, not a
    // wrong verdict today.
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
    // Sound reconciliation: never a wrong verdict. `unknown` today; a future
    // free-division-witness route may promote this to `sat` (matching Z3).
    assert!(
        matches!(r, CheckResult::Unknown(_)),
        "x/0 divergence must be a sound unknown, not a wrong verdict, got {r:?}"
    );
}

#[test]
fn mixed_sign_product_cannot_be_positive() {
    // x > 0 ∧ y < 0 ∧ x*y > 0 is unsat: opposite signs give a non-positive
    // product (the (a≥0 ∧ b≤0) → r≤0 sign lemma), with no model needed.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let zero = a.real_const(Rational::integer(0));
    let xpos = a.real_gt(x, zero).unwrap();
    let yneg = a.real_lt(y, zero).unwrap();
    let p = a.real_mul(x, y).unwrap();
    let ppos = a.real_gt(p, zero).unwrap();
    let r = check_with_nra(&mut a, &[xpos, yneg, ppos], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "pos*neg>0 must be unsat, got {r:?}"
    );
}

#[test]
fn zero_square_forces_zero_base() {
    // x*x == 0 ∧ x != 0 is unsat: the zero rule's reverse direction
    // (r=0 → a=0 ∨ b=0) with a=b=x forces x=0.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let zero = a.real_const(Rational::integer(0));
    let sq = a.real_mul(x, x).unwrap();
    let sq_zero = a.eq(sq, zero).unwrap();
    let x_eq_zero = a.eq(x, zero).unwrap();
    let x_ne_zero = a.not(x_eq_zero).unwrap();
    let r = check_with_nra(&mut a, &[sq_zero, x_ne_zero], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "x*x=0 ∧ x≠0 must be unsat, got {r:?}"
    );
}

#[test]
fn sum_of_three_unbounded_squares_plus_one_is_unsat() {
    // x²+y²+z²+1 = 0 with NO bounds: unsat over the reals (a sum of squares is
    // ≥ 0, so the LHS is ≥ 1 > 0). Regression coverage for *multi-variable*
    // square infeasibility (the existing tests cover a single square): the sign
    // rules `(x≥0∨x≤0)→x²≥0` decide it, via the Boolean solver resolving the
    // per-variable sign splits. (A measured check confirmed the conditional rules
    // already crack this without an unconditional `x²≥0` lemma — so no such lemma
    // is added; this pins the behavior as a regression guard.)
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let z = real(&mut a, "z");
    let xx = a.real_mul(x, x).unwrap();
    let yy = a.real_mul(y, y).unwrap();
    let zz = a.real_mul(z, z).unwrap();
    let one = a.real_const(Rational::integer(1));
    let s1 = a.real_add(xx, yy).unwrap();
    let s2 = a.real_add(s1, zz).unwrap();
    let s3 = a.real_add(s2, one).unwrap();
    let zero = a.real_const(Rational::integer(0));
    let eq0 = a.eq(s3, zero).unwrap();

    let r = check_with_nra(&mut a, &[eq0], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "x²+y²+z²+1=0 (unbounded) must be unsat, got {r:?}"
    );
}

/// **Sum-of-squares lemma (AM–GM₂).** `a²+b² ≥ 2ab` holds for all reals (it is
/// `(a−b)² ≥ 0`), so its negation `a²+b² < 2ab` is UNSAT. Plain product abstraction
/// abstracts `a²`, `b²`, `ab` independently and leaves this `unknown`; the SOS lemma
/// `r_aa + r_bb − 2·r_ab ≥ 0` closes it.
#[test]
fn sum_of_squares_am_gm_is_unsat() {
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let xx = a.real_mul(x, x).unwrap();
    let yy = a.real_mul(y, y).unwrap();
    let xy = a.real_mul(x, y).unwrap();
    let sum = a.real_add(xx, yy).unwrap(); // x² + y²
    let two = a.real_const(Rational::integer(2));
    let two_xy = a.real_mul(two, xy).unwrap(); // 2xy
    let neg = a.real_lt(sum, two_xy).unwrap(); // x² + y² < 2xy  (negation of AM–GM)

    let r = check_with_nra(&mut a, &[neg], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "x²+y² < 2xy must be unsat (it is −(x−y)² < 0), got {r:?}"
    );
}

/// The SOS lemma must not over-claim: `x²+y² = 2xy` IS satisfiable (any `x=y`), so
/// the solver must not wrongly refute it.
#[test]
fn sum_of_squares_equality_is_satisfiable() {
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let xx = a.real_mul(x, x).unwrap();
    let yy = a.real_mul(y, y).unwrap();
    let xy = a.real_mul(x, y).unwrap();
    let sum = a.real_add(xx, yy).unwrap();
    let two = a.real_const(Rational::integer(2));
    let two_xy = a.real_mul(two, xy).unwrap();
    let eq = a.eq(sum, two_xy).unwrap(); // x² + y² = 2xy  (true iff x = y)

    let r = check_with_nra(&mut a, &[eq], &SolverConfig::default()).unwrap();
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x²+y² = 2xy is sat (x=y), must not be refuted, got {r:?}"
    );
}

/// Build `a²+b²+c² ⋈ ab+bc+ca` (three squares + three cross-products `ab`,`bc`,`ca`)
/// optionally with `[-1,1]` bounds on each variable, returning the assertion list.
/// `op` builds the top-level comparison (e.g. `real_lt`).
fn three_var_cross_query(bounded: bool) -> (TermArena, Vec<axeyum_ir::TermId>) {
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let z = real(&mut a, "z");
    let mut assertions = Vec::new();
    if bounded {
        let neg_one = a.real_const(Rational::integer(-1));
        let one = a.real_const(Rational::integer(1));
        for v in [x, y, z] {
            assertions.push(a.real_ge(v, neg_one).unwrap());
            assertions.push(a.real_le(v, one).unwrap());
        }
    }
    let xx = a.real_mul(x, x).unwrap();
    let yy = a.real_mul(y, y).unwrap();
    let zz = a.real_mul(z, z).unwrap();
    let xy = a.real_mul(x, y).unwrap();
    let yz = a.real_mul(y, z).unwrap();
    let zx = a.real_mul(z, x).unwrap();
    let s1 = a.real_add(xx, yy).unwrap();
    let lhs = a.real_add(s1, zz).unwrap();
    let r1 = a.real_add(xy, yz).unwrap();
    let rhs = a.real_add(r1, zx).unwrap();
    let lt = a.real_lt(lhs, rhs).unwrap();
    assertions.push(lt);
    (a, assertions)
}

/// 3-variable AM–GM: `a²+b²+c² < ab+bc+ca` over **unbounded** reals is globally
/// unsatisfiable (`a²+b²+c²−ab−bc−ca = ½[(a−b)²+(b−c)²+(c−a)²] ≥ 0`). The strict
/// `< 0` refutation is now decided **Unsat** by the degree-2 SOS/PSD certificate
/// (ADR-0039), which runs in `decide_real_poly_constraint` *before* the abstraction
/// search. This is a strict improvement: the query historically OOM-killed the host
/// and was then merely *declined* by the `MAX_CROSS_PRODUCTS` admission bound; the
/// SOS certificate now proves it exactly and instantly. Sound Unsat, never a wrong
/// sat. (The indefinite companion form `ab+bc+ca < −1`, which the SOS certificate
/// correctly declines, is now decided **Sat** by the recursive strict CAD — see
/// `indefinite_three_cross_products_decided_sat_by_strict_cad` below.)
#[test]
fn unbounded_three_variable_am_gm_is_proved_unsat_by_sos() {
    let (mut a, assertions) = three_var_cross_query(false);
    let r = check_with_nra(&mut a, &assertions, &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "3-var AM–GM a²+b²+c²<ab+bc+ca is globally unsat (SOS); got {r:?}"
    );
}

/// The same AM–GM query with **every variable bounded** to `[-1,1]`. The strict
/// quadratic atom is globally PSD-refuted regardless of the (linear) bounds, so the
/// SOS certificate still proves **Unsat**. Pins that the SOS decision is
/// bound-independent.
#[test]
fn bounded_three_variable_am_gm_is_proved_unsat_by_sos() {
    let (mut a, assertions) = three_var_cross_query(true);
    let r = check_with_nra(&mut a, &assertions, &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "bounded 3-var AM–GM is globally unsat (SOS, bound-independent); got {r:?}"
    );
}

/// An *indefinite* three-cross-product STRICT query `ab+bc+ca < −1`. The form
/// `ab+bc+ca` is indefinite (eigenvalues `1, −½, −½`), so it is neither PSD nor NSD
/// and the degree-2 SOS certificate correctly **declines**. It is genuinely
/// SATISFIABLE (e.g. `a=2, b=−1, c=0` ⇒ `−2+0+0 = −2 < −1`), and the recursive
/// N-variable strict CAD (all atoms strict ⇒ the solution set is open ⇒ rational
/// interior cell samples decide it exactly) now finds a rational witness, replacing
/// the former `ResourceLimit` `Unknown` degrade. Must be a SOUND Sat (replays
/// through the independent ground evaluator) — never an OOM/crash, and never a wrong
/// Unsat (the form is unbounded below).
#[test]
fn indefinite_three_cross_products_decided_sat_by_strict_cad() {
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let z = real(&mut a, "z");
    let xy = a.real_mul(x, y).unwrap();
    let yz = a.real_mul(y, z).unwrap();
    let zx = a.real_mul(z, x).unwrap();
    let s1 = a.real_add(xy, yz).unwrap();
    let form = a.real_add(s1, zx).unwrap(); // ab + bc + ca (indefinite)
    let neg_one = a.real_const(Rational::integer(-1));
    let lt = a.real_lt(form, neg_one).unwrap(); // ab+bc+ca < −1
    let r = check_with_nra(&mut a, &[lt], &SolverConfig::default()).unwrap();
    // Never a wrong Unsat (the form is unbounded below ⇒ the region is nonempty).
    assert!(
        !matches!(r, CheckResult::Unsat),
        "ab+bc+ca < −1 is sat (e.g. (2,−1,0)); must NEVER be Unsat, got {r:?}"
    );
    // A Sat witness must replay through the independent ground evaluator.
    if let CheckResult::Sat(model) = &r {
        let asg = model.to_assignment();
        assert!(
            matches!(
                axeyum_ir::eval(&a, lt, &asg),
                Ok(axeyum_ir::Value::Bool(true))
            ),
            "the strict-CAD witness must replay ab+bc+ca < −1 true; got {r:?}"
        );
    }
}

/// Selectivity: the guard counts **cross-products**, not squares. A square-only
/// multi-variable instance (`x²+y²+z²+1 = 0`, three squares, zero cross-products) is
/// **not** gated and is still decided `unsat` (also covered by
/// `sum_of_three_unbounded_squares_plus_one_is_unsat`; pinned here against the bound
/// to document that squares never trip it). The 2-variable SOS frontier
/// (`a²+b² < 2ab`, one cross-product) likewise stays decidable — see
/// `sum_of_squares_am_gm_is_unsat`.
#[test]
fn square_only_multivariable_is_not_gated_by_cross_product_bound() {
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let z = real(&mut a, "z");
    let xx = a.real_mul(x, x).unwrap();
    let yy = a.real_mul(y, y).unwrap();
    let zz = a.real_mul(z, z).unwrap();
    let one = a.real_const(Rational::integer(1));
    let s1 = a.real_add(xx, yy).unwrap();
    let s2 = a.real_add(s1, zz).unwrap();
    let s3 = a.real_add(s2, one).unwrap();
    let zero = a.real_const(Rational::integer(0));
    let eq0 = a.eq(s3, zero).unwrap();

    let r = check_with_nra(&mut a, &[eq0], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "square-only x²+y²+z²+1=0 must stay decidable (unsat), not be gated, got {r:?}"
    );
}
