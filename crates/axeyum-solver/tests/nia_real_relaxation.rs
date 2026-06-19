//! Real relaxation of integer-nonlinear queries (G3): integers ⊆ reals, so an
//! integer query is `unsat` whenever its faithful real relaxation is `unsat`.
//! This refutes sign-based integer-NIA goals (`x*x < 0`) that the bounded
//! integer bit-blaster only ever reports as `unknown`, and — through the
//! valid-universal pass — decides `∀x:Int. x*x >= 0` as `sat`. Strictly
//! additive: it only sharpens `unknown` to `unsat` for the real-refutable cases,
//! never overturning a decided `sat`/`unsat`.
#![allow(clippy::many_single_char_names)]

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{CheckResult, SolverConfig, check_auto, solve};

#[test]
fn int_square_negative_is_unsat() {
    // x*x < 0 over the integers: a square is >= 0, so unsat. The width ladder
    // returns unknown; the real relaxation refutes it via the NRA sign rules.
    let mut a = TermArena::new();
    let x = a.int_var("x").unwrap();
    let xx = a.int_mul(x, x).unwrap();
    let zero = a.int_const(0);
    let lt = a.int_lt(xx, zero).unwrap();

    let r = check_auto(&mut a, &[lt], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "x*x < 0 (Int) must be unsat, got {r:?}"
    );
}

#[test]
fn int_square_plus_one_nonpositive_is_unsat() {
    // x*x + 1 <= 0 over the integers: x*x >= 0 so x*x + 1 >= 1 > 0 — unsat.
    let mut a = TermArena::new();
    let x = a.int_var("x").unwrap();
    let xx = a.int_mul(x, x).unwrap();
    let one = a.int_const(1);
    let sum = a.int_add(xx, one).unwrap();
    let zero = a.int_const(0);
    let le = a.int_le(sum, zero).unwrap();

    let r = check_auto(&mut a, &[le], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "x*x + 1 <= 0 (Int) must be unsat, got {r:?}"
    );
}

#[test]
fn forall_int_square_nonnegative_is_sat() {
    // ∀x:Int. x*x >= 0 — valid. The valid-universal pass proves validity by
    // deciding ¬body[x:=c] = (c*c < 0) unsat; that integer-NIA refutation now
    // succeeds through the real relaxation, so the universal becomes sat.
    let mut a = TermArena::new();
    let xsym = a.declare("x", Sort::Int).unwrap();
    let xv = a.var(xsym);
    let xx = a.int_mul(xv, xv).unwrap();
    let zero = a.int_const(0);
    let ge = a.int_ge(xx, zero).unwrap();
    let body = a.forall(xsym, ge).unwrap();

    let r = solve(&mut a, &[body], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Sat(_)),
        "∀x:Int. x*x >= 0 must be sat, got {r:?}"
    );
}

#[test]
fn int_square_equals_two_stays_unknown() {
    // x*x == 2 over the integers: integer-unsat (no integer root of 2) but
    // real-SAT (x = √2), so the relaxation cannot refute it. Must stay unknown —
    // never a wrong unsat.
    let mut a = TermArena::new();
    let x = a.int_var("x").unwrap();
    let xx = a.int_mul(x, x).unwrap();
    let two = a.int_const(2);
    let eq = a.eq(xx, two).unwrap();

    let r = check_auto(&mut a, &[eq], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unknown(_)),
        "x*x == 2 (Int) must stay unknown (real-sat), got {r:?}"
    );
}

#[test]
fn int_square_equals_four_positive_is_sat() {
    // x*x == 4 ∧ x > 0 over the integers: genuine witness x = 2. The width
    // ladder decides this as sat before the relaxation runs — the relaxation
    // (which only ever yields unsat) must not interfere.
    let mut a = TermArena::new();
    let x = a.int_var("x").unwrap();
    let xx = a.int_mul(x, x).unwrap();
    let four = a.int_const(4);
    let eq = a.eq(xx, four).unwrap();
    let zero = a.int_const(0);
    let pos = a.int_gt(x, zero).unwrap();

    let r = check_auto(&mut a, &[eq, pos], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Sat(_)),
        "x*x == 4 ∧ x > 0 (Int) must be sat (x=2), got {r:?}"
    );
}
