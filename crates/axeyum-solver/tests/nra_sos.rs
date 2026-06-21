//! Degree-2 sum-of-squares / positive-semidefinite (PSD) refutation for the NRA
//! engine: a STRICT inequality atom whose polynomial is a globally one-signed
//! quadratic form is refuted everywhere, so its strict comparison is **Unsat**.
//!
//! Sound, possibly incomplete: PSD of the Gram matrix `M` of `p` proves
//! `p(x) ≥ 0 ∀x` (⇒ `p < 0` Unsat); `−M` PSD proves `p(x) ≤ 0 ∀x` (⇒ `p > 0`
//! Unsat). It NEVER concludes Unsat for non-strict `≤`/`≥` atoms (PSD gives
//! `≥ 0`, not `> 0`) and NEVER produces a wrong Sat; in every other shape it
//! declines and the verdict comes from the rest of the NRA stack. All arithmetic
//! is exact over `Rational` — no floating point.
//!
//! Headline case (previously declined): the 3-variable AM-GM refutation
//! `a²+b²+c²−ab−bc−ca < 0` is now decided **Unsat**.

use axeyum_ir::{Rational, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn real(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, Sort::Real).unwrap();
    arena.var(s)
}

fn konst(arena: &mut TermArena, c: i128) -> TermId {
    arena.real_const(Rational::integer(c))
}

fn run(arena: &mut TermArena, assertion: TermId) -> CheckResult {
    solve(arena, &[assertion], &SolverConfig::default()).expect("solve must not error")
}

fn is_unsat(r: &CheckResult) -> bool {
    matches!(r, CheckResult::Unsat)
}

// ---------------------------------------------------------------------------
// Globally one-signed strict inequalities ⇒ Unsat.
// ---------------------------------------------------------------------------

#[test]
fn am_gm_two_var_is_unsat() {
    // Refute x²+y² ≥ 2xy ⇒ atom x²+y²−2xy < 0 (= (x−y)² < 0) ⇒ Unsat.
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let xx = arena.real_mul(x, x).unwrap();
    let yy = arena.real_mul(y, y).unwrap();
    let xy = arena.real_mul(x, y).unwrap();
    let two = konst(&mut arena, 2);
    let two_xy = arena.real_mul(two, xy).unwrap();
    let sum = arena.real_add(xx, yy).unwrap();
    let p = arena.real_sub(sum, two_xy).unwrap();
    let zero = konst(&mut arena, 0);
    let atom = arena.real_lt(p, zero).unwrap();

    let result = run(&mut arena, atom);
    assert!(
        is_unsat(&result),
        "(x−y)² < 0 must be Unsat, got {result:?}"
    );
}

#[test]
fn am_gm_three_var_is_unsat() {
    // THE headline case (previously declined): refute a²+b²+c² ≥ ab+bc+ca ⇒
    // atom a²+b²+c²−ab−bc−ca < 0 (= ½[(a−b)²+(b−c)²+(c−a)²] < 0) ⇒ Unsat.
    let mut arena = TermArena::new();
    let a = real(&mut arena, "a");
    let b = real(&mut arena, "b");
    let c = real(&mut arena, "c");
    let aa = arena.real_mul(a, a).unwrap();
    let bb = arena.real_mul(b, b).unwrap();
    let cc = arena.real_mul(c, c).unwrap();
    let ab = arena.real_mul(a, b).unwrap();
    let bc = arena.real_mul(b, c).unwrap();
    let ca = arena.real_mul(c, a).unwrap();
    let squares = {
        let s = arena.real_add(aa, bb).unwrap();
        arena.real_add(s, cc).unwrap()
    };
    let cross = {
        let s = arena.real_add(ab, bc).unwrap();
        arena.real_add(s, ca).unwrap()
    };
    let p = arena.real_sub(squares, cross).unwrap();
    let zero = konst(&mut arena, 0);
    let atom = arena.real_lt(p, zero).unwrap();

    let result = run(&mut arena, atom);
    assert!(
        is_unsat(&result),
        "a²+b²+c²−ab−bc−ca < 0 must be Unsat, got {result:?}"
    );
}

#[test]
fn affine_square_is_unsat() {
    // x²−2x+1 < 0 (= (x−1)² < 0) ⇒ Unsat. Exercises the bordered/affine matrix.
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let xx = arena.real_mul(x, x).unwrap();
    let two = konst(&mut arena, 2);
    let two_x = arena.real_mul(two, x).unwrap();
    let one = konst(&mut arena, 1);
    let p = {
        let t = arena.real_sub(xx, two_x).unwrap();
        arena.real_add(t, one).unwrap()
    };
    let zero = konst(&mut arena, 0);
    let atom = arena.real_lt(p, zero).unwrap();

    let result = run(&mut arena, atom);
    assert!(
        is_unsat(&result),
        "(x−1)² < 0 must be Unsat, got {result:?}"
    );
}

#[test]
fn negative_definite_strict_gt_is_unsat() {
    // −(x²+y²) > 0 ⇒ Unsat (the NSD branch: −M PSD ⇒ p ≤ 0 everywhere).
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let xx = arena.real_mul(x, x).unwrap();
    let yy = arena.real_mul(y, y).unwrap();
    let sum = arena.real_add(xx, yy).unwrap();
    let p = arena.real_neg(sum).unwrap();
    let zero = konst(&mut arena, 0);
    let atom = arena.real_gt(p, zero).unwrap();

    let result = run(&mut arena, atom);
    assert!(
        is_unsat(&result),
        "−(x²+y²) > 0 must be Unsat, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// SOUND-NEGATIVE: must NOT be a wrong Unsat (sat or decline, never Unsat).
// ---------------------------------------------------------------------------

#[test]
fn indefinite_x2_minus_y2_not_unsat() {
    // x²−y² < 0 is satisfiable (e.g. x=0, y=1) ⇒ must NOT be Unsat.
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let xx = arena.real_mul(x, x).unwrap();
    let yy = arena.real_mul(y, y).unwrap();
    let p = arena.real_sub(xx, yy).unwrap();
    let zero = konst(&mut arena, 0);
    let atom = arena.real_lt(p, zero).unwrap();

    let result = run(&mut arena, atom);
    assert!(
        !is_unsat(&result),
        "x²−y² < 0 is satisfiable; must NOT be Unsat, got {result:?}"
    );
}

#[test]
fn bilinear_xy_not_unsat() {
    // x*y < 0 is indefinite/satisfiable (x=1, y=−1) ⇒ must NOT be Unsat.
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let xy = arena.real_mul(x, y).unwrap();
    let zero = konst(&mut arena, 0);
    let atom = arena.real_lt(xy, zero).unwrap();

    let result = run(&mut arena, atom);
    assert!(
        !is_unsat(&result),
        "x*y < 0 is satisfiable; must NOT be Unsat, got {result:?}"
    );
}

#[test]
fn nonstrict_psd_not_unsat() {
    // x²+y²−2xy ≤ 0 (= (x−y)² ≤ 0) is satisfiable at x=y ⇒ must NOT be Unsat
    // (PSD gives ≥ 0; the non-strict ≤ 0 is SAT at the zero, not unsat).
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let xx = arena.real_mul(x, x).unwrap();
    let yy = arena.real_mul(y, y).unwrap();
    let xy = arena.real_mul(x, y).unwrap();
    let two = konst(&mut arena, 2);
    let two_xy = arena.real_mul(two, xy).unwrap();
    let sum = arena.real_add(xx, yy).unwrap();
    let p = arena.real_sub(sum, two_xy).unwrap();
    let zero = konst(&mut arena, 0);
    let atom = arena.real_le(p, zero).unwrap();

    let result = run(&mut arena, atom);
    assert!(
        !is_unsat(&result),
        "(x−y)² ≤ 0 is satisfiable at x=y; must NOT be Unsat, got {result:?}"
    );
}

#[test]
fn degree_three_declines() {
    // x*x*x < 0 is satisfiable (x = −1) ⇒ the degree-2 certificate must NOT fire
    // and must NOT yield a wrong Unsat.
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let xx = arena.real_mul(x, x).unwrap();
    let xxx = arena.real_mul(xx, x).unwrap();
    let zero = konst(&mut arena, 0);
    let atom = arena.real_lt(xxx, zero).unwrap();

    let result = run(&mut arena, atom);
    assert!(
        !is_unsat(&result),
        "x³ < 0 is satisfiable; must NOT be Unsat, got {result:?}"
    );
}
