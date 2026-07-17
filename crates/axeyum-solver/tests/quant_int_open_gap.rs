//! Exact decision of **open, constant-width-gap** single-variable integer
//! universals.
//!
//! An *open* `∀x:Int. φ` whose Fourier-Motzkin bounds on `x` are *symbolic*
//! (mention free parameters) is normally undecidable by the closed integer path
//! (which needs concrete rational endpoints) and by the real-validity relaxation
//! (which ignores integrality). But when every clause of `¬φ` carves out an
//! interval `[L, U]` of **constant width** `U − L` over **integer-valued**
//! endpoints, its integer content is *translation-invariant*: the same count of
//! integers for every parameter assignment. So:
//!
//! - if any clause's interval ALWAYS contains an integer ⇒ `∃x:Int. ¬φ` holds for
//!   all parameters ⇒ `∀x:Int. φ` is false in every model ⇒ `unsat`;
//! - else if every clause NEVER contains an integer ⇒ `∀x:Int. φ` is valid ⇒ the
//!   assertion rewrites to `true` ⇒ `sat`.
//!
//! The canonical decided case is `∀x:Int. (x ≤ y ∨ x ≥ y + 2)` — `¬φ` is the open
//! interval `(y, y + 2)` of width 2, which contains `y + 1` for every integer
//! `y` ⇒ `unsat` (z3 agrees). The `k = 1` sibling `∀x:Int. (x ≤ y ∨ x ≥ y + 1)`
//! is the open `(y, y + 1)`, width 1, no integer ⇒ valid ⇒ `sat`.
//!
//! The suite also pins the SOUNDNESS NEGATIVES the open-gap path must NOT mis-
//! decide: a *distinct-parameter* gap `(y, z + 2)` has symbolic (non-constant)
//! width ⇒ must DECLINE (never a bogus verdict); a width-1 multiple-coefficient
//! gap `(2y, 2y + 1)` is valid (2y is an integer) ⇒ must be `sat`, never `unsat`;
//! a non-linear universal must DECLINE.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

fn check(arena: &mut TermArena, assertions: &[TermId]) -> CheckResult {
    solve(arena, assertions, &config()).expect("solve decides or returns unknown without error")
}

fn assert_sat(arena: &mut TermArena, assertions: &[TermId]) {
    assert!(
        matches!(check(arena, assertions), CheckResult::Sat(_)),
        "expected sat (integer-valid universal ⇒ the assertion is satisfiable)"
    );
}

fn assert_unsat(arena: &mut TermArena, assertions: &[TermId]) {
    assert!(
        matches!(check(arena, assertions), CheckResult::Unsat),
        "expected unsat (the integer universal is false in every model)"
    );
}

fn assert_not_unsat(arena: &mut TermArena, assertions: &[TermId]) {
    // Soundness negative: must NOT be a bogus `unsat`. Sat or unknown are fine.
    assert!(
        !matches!(check(arena, assertions), CheckResult::Unsat),
        "unsound: a satisfiable / undecidable universal was wrongly reported unsat"
    );
}

fn assert_not_sat(arena: &mut TermArena, assertions: &[TermId]) {
    // Soundness negative: must NOT be a bogus `sat`. Unsat or unknown are fine.
    assert!(
        !matches!(check(arena, assertions), CheckResult::Sat(_)),
        "unsound: an unsatisfiable / undecidable universal was wrongly reported sat"
    );
}

fn int(arena: &mut TermArena, name: &str) -> (SymbolId, TermId) {
    let s = arena.declare(name, Sort::Int).unwrap();
    let v = arena.var(s);
    (s, v)
}

/// Builds `∀x:Int. (x ≤ low ∨ x ≥ high)` where `low`/`high` are caller-supplied
/// `x`-free integer terms. `¬φ` is the open interval `(low, high)`.
fn forall_gap(arena: &mut TermArena, low: TermId, high: TermId) -> (SymbolId, TermId) {
    let (x_sym, x) = int(arena, "x");
    let le_low = arena.int_le(x, low).unwrap();
    let ge_high = arena.int_ge(x, high).unwrap();
    let body = arena.or(le_low, ge_high).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    (x_sym, forall)
}

// ---------------------------------------------------------------------------
// DECIDES UNSAT — open gaps whose constant-width interval always holds an integer.
// ---------------------------------------------------------------------------

#[test]
fn forall_int_le_y_or_ge_y_plus_2_is_unsat() {
    // ∀x:Int. (x ≤ y ∨ x ≥ y + 2). `¬φ = (x > y ∧ x < y + 2)` = open `(y, y + 2)`,
    // width 2, which contains `y + 1` for EVERY integer y ⇒ the universal is false
    // in every model ⇒ unsat (z3 decides this; this is the flagged completeness
    // item the open-gap path closes).
    let mut arena = TermArena::new();
    let (_y_sym, y) = int(&mut arena, "y");
    let two = arena.int_const(2);
    let y_plus_2 = arena.int_add(y, two).unwrap();
    let (_x_sym, forall) = forall_gap(&mut arena, y, y_plus_2);
    assert_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_int_le_y_or_ge_y_plus_3_is_unsat() {
    // ∀x:Int. (x ≤ y ∨ x ≥ y + 3). Open `(y, y + 3)`, width 3, contains `y + 1`
    // and `y + 2` ⇒ unsat.
    let mut arena = TermArena::new();
    let (_y_sym, y) = int(&mut arena, "y");
    let three = arena.int_const(3);
    let y_plus_3 = arena.int_add(y, three).unwrap();
    let (_x_sym, forall) = forall_gap(&mut arena, y, y_plus_3);
    assert_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_int_le_y_minus_1_or_ge_y_plus_1_is_unsat() {
    // ∀x:Int. (x ≤ y - 1 ∨ x ≥ y + 1). Open `(y - 1, y + 1)`, width 2, contains
    // `y` for every integer y ⇒ unsat. (Endpoints carry both a +1 and a -1
    // constant; the symbolic `y` parts still cancel to a constant width.)
    let mut arena = TermArena::new();
    let (_y_sym, y) = int(&mut arena, "y");
    let one = arena.int_const(1);
    let y_minus_1 = arena.int_sub(y, one).unwrap();
    let y_plus_1 = arena.int_add(y, one).unwrap();
    let (_x_sym, forall) = forall_gap(&mut arena, y_minus_1, y_plus_1);
    assert_unsat(&mut arena, &[forall]);
}

// ---------------------------------------------------------------------------
// DECIDES SAT — open gaps whose constant-width interval never holds an integer.
// ---------------------------------------------------------------------------

#[test]
fn forall_int_le_y_or_ge_y_plus_1_is_sat() {
    // ∀x:Int. (x ≤ y ∨ x ≥ y + 1). Open `(y, y + 1)`, width 1, contains NO integer
    // for any integer y ⇒ the universal is valid ⇒ sat (rewrites to `true`).
    let mut arena = TermArena::new();
    let (_y_sym, y) = int(&mut arena, "y");
    let one = arena.int_const(1);
    let y_plus_1 = arena.int_add(y, one).unwrap();
    let (_x_sym, forall) = forall_gap(&mut arena, y, y_plus_1);
    assert_sat(&mut arena, &[forall]);
}

#[test]
fn forall_int_2y_gap_width_1_is_sat_not_unsat() {
    // ∀x:Int. (x ≤ 2y ∨ x ≥ 2y + 1). Open `(2y, 2y + 1)`, width 1. The lower
    // endpoint `2y` is integer-valued (coefficient 2 is an integer), so the
    // interval contains NO integer ⇒ valid ⇒ sat. SOUNDNESS NEGATIVE: a coefficient
    // > 1 must NOT trip a bogus `unsat`.
    let mut arena = TermArena::new();
    let (_y_sym, y) = int(&mut arena, "y");
    let two = arena.int_const(2);
    let one = arena.int_const(1);
    let two_y = arena.int_mul(two, y).unwrap();
    let two_y_plus_1 = arena.int_add(two_y, one).unwrap();
    let (_x_sym, forall) = forall_gap(&mut arena, two_y, two_y_plus_1);
    assert_sat(&mut arena, &[forall]);
    assert_not_unsat(&mut arena, &[forall]);
}

// ---------------------------------------------------------------------------
// SOUNDNESS NEGATIVES — must DECLINE (never a wrong verdict).
// ---------------------------------------------------------------------------

#[test]
fn forall_int_distinct_params_gap_is_not_misdecided() {
    // ∀x:Int. (x ≤ y ∨ x ≥ z + 2) with DISTINCT params y, z. `¬φ` is the interval
    // `(y, z + 2)` of SYMBOLIC width `z - y + 2` — NOT constant. The truth depends
    // on the relation of y and z (false when z + 2 - y > 1, i.e. there is an
    // integer between; vacuously true when the interval is empty). So this is
    // genuinely PARAMETER-DEPENDENT and the open-gap path must DECLINE — it must
    // not report a global `sat` or `unsat`.
    let mut arena = TermArena::new();
    let (_y_sym, y) = int(&mut arena, "y");
    let (_z_sym, z) = int(&mut arena, "z");
    let two = arena.int_const(2);
    let z_plus_2 = arena.int_add(z, two).unwrap();
    let (_x_sym, forall) = forall_gap(&mut arena, y, z_plus_2);
    // Neither verdict is globally correct here ⇒ must be undecided (unknown).
    assert_not_unsat(&mut arena, &[forall]);
    assert_not_sat(&mut arena, &[forall]);
}

#[test]
fn forall_int_nonlinear_declines() {
    // ∀x:Int. x * x ≥ 0 — non-linear in x ⇒ outside the affine fragment ⇒ the
    // open-gap path declines (the affine collector rejects the product). It must
    // not be wrongly decided by THIS path; the body is in fact valid, so the only
    // forbidden outcome is a bogus `unsat`.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let zero = arena.int_const(0);
    let x_sq = arena.int_mul(x, x).unwrap();
    let body = arena.int_ge(x_sq, zero).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_not_unsat(&mut arena, &[forall]);
}

// ---------------------------------------------------------------------------
// COMPANION DISPATCH — the `true`-rewrite must not mask other assertions.
// ---------------------------------------------------------------------------

#[test]
fn forall_int_open_gap_true_rewrite_then_extra_constraint() {
    // ∀x:Int. (x ≤ y ∨ x ≥ y + 1) rewrites to `true`; a separate satisfiable
    // assertion (w = 7) leaves the whole query SAT.
    let mut arena = TermArena::new();
    let (_y_sym, y) = int(&mut arena, "y");
    let one = arena.int_const(1);
    let y_plus_1 = arena.int_add(y, one).unwrap();
    let (_x_sym, forall) = forall_gap(&mut arena, y, y_plus_1);
    let (_w_sym, w) = int(&mut arena, "w");
    let seven = arena.int_const(7);
    let w_is_7 = arena.eq(w, seven).unwrap();
    assert_sat(&mut arena, &[forall, w_is_7]);
}

#[test]
fn forall_int_open_gap_unsat_dominates_companion() {
    // ∀x:Int. (x ≤ y ∨ x ≥ y + 2) is unsat (false in every model); adding any
    // companion assertion cannot rescue it ⇒ the whole query stays unsat.
    let mut arena = TermArena::new();
    let (_y_sym, y) = int(&mut arena, "y");
    let two = arena.int_const(2);
    let y_plus_2 = arena.int_add(y, two).unwrap();
    let (_x_sym, forall) = forall_gap(&mut arena, y, y_plus_2);
    let (_w_sym, w) = int(&mut arena, "w");
    let five = arena.int_const(5);
    let w_is_5 = arena.eq(w, five).unwrap();
    assert_unsat(&mut arena, &[forall, w_is_5]);
}
