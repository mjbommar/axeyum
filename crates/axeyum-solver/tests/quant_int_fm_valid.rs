//! Sound, one-directional **integer** relaxation of the real Fourier-Motzkin
//! universal pass.
//!
//! For a top-level `∀x:Int. φ`, the pass runs the *real* FM elimination
//! (treating `x` as a real) and rewrites the assertion to `true` **iff and only
//! iff** the real relaxation `∀x:Real. φ` is *valid* — because `ℤ ⊆ ℝ` makes a
//! real-valid universal integer-valid. This direction is sound; the converse is
//! **not** (an integer universal can hold where the real universal fails, the
//! counterexample landing in a gap between integers).
//!
//! These tests pin both the newly-decided integer-valid universals **and** the
//! soundness negatives the relaxation must NOT mis-decide:
//!
//! - `∀x:Int. (x ≤ 0 ∨ x ≥ 1)` — integer-VALID but real-INVALID (the real hole
//!   is `0 < x < 1`); the real-FM verdict is *not valid*, so the integer path
//!   declines. It must NEVER be turned into a bogus `unsat`.
//! - `∀x:Int. (x ≥ 0 ∧ x ≤ 10)` — integer-FALSE and real-FALSE; the integer
//!   path declines (real verdict is `unsat`, which is *not* the valid verdict).
//!   The genuine `unsat` comes from the other passes and must NOT become `sat`.
//! - `∀x:Int. x > 0` — already `unsat` via the single-atom unsat-∀ pass; the
//!   integer relaxation must not interfere / must not make it `sat`.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, TermId};
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
        "expected unsat"
    );
}

fn assert_not_sat(arena: &mut TermArena, assertions: &[TermId]) {
    // Soundness negative: must NOT be a bogus `sat`. Unsat or unknown are fine.
    assert!(
        !matches!(check(arena, assertions), CheckResult::Sat(_)),
        "unsound: an unsatisfiable / undecidable universal was wrongly reported sat"
    );
}

fn assert_not_unsat(arena: &mut TermArena, assertions: &[TermId]) {
    // Soundness negative: must NOT be a bogus `unsat`. Sat or unknown are fine.
    assert!(
        !matches!(check(arena, assertions), CheckResult::Unsat),
        "unsound: a satisfiable / undecidable universal was wrongly reported unsat"
    );
}

fn int(arena: &mut TermArena, name: &str) -> (axeyum_ir::SymbolId, TermId) {
    let s = arena.declare(name, Sort::Int).unwrap();
    let v = arena.var(s);
    (s, v)
}

// ---------------------------------------------------------------------------
// DECIDES — integer universals whose real relaxation is VALID.
// ---------------------------------------------------------------------------

#[test]
fn forall_int_le0_or_gt0_is_valid_sat() {
    // ∀x:Int. (x ≤ 0 ∨ x > 0) — real-valid (trichotomy at 0) ⇒ integer-valid ⇒
    // the assertion is satisfiable. Decided by the integer relaxation.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let zero = arena.int_const(0);
    let le0 = arena.int_le(x, zero).unwrap();
    let gt0 = arena.int_gt(x, zero).unwrap();
    let body = arena.or(le0, gt0).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[forall]);
}

#[test]
fn forall_int_lt5_or_ge5_is_valid_sat() {
    // ∀x:Int. (x < 5 ∨ x ≥ 5) — real-valid (trichotomy at 5) ⇒ integer-valid.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let five = arena.int_const(5);
    let lt5 = arena.int_lt(x, five).unwrap();
    let ge5 = arena.int_ge(x, five).unwrap();
    let body = arena.or(lt5, ge5).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[forall]);
}

// ---------------------------------------------------------------------------
// SOUNDNESS NEGATIVES — must never be wrongly decided by the relaxation.
// ---------------------------------------------------------------------------

#[test]
fn forall_int_le0_or_ge1_not_misdecided() {
    // ∀x:Int. (x ≤ 0 ∨ x ≥ 1) — integer-VALID (no integer in the open (0,1)),
    // but real-INVALID (x = 0.5 falsifies). The real-FM verdict is *not valid*,
    // so the integer relaxation DECLINES. The crux: it must NOT be turned into a
    // bogus `unsat` (the real-`unsat` verdict is forbidden on the integer path).
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let le0 = arena.int_le(x, zero).unwrap();
    let ge1 = arena.int_ge(x, one).unwrap();
    let body = arena.or(le0, ge1).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    // The integer universal is genuinely TRUE, so it must never be `unsat`.
    assert_not_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_int_ge0_and_le10_not_sat() {
    // ∀x:Int. (x ≥ 0 ∧ x ≤ 10) — integer-FALSE and real-FALSE (x = -1). The real
    // relaxation's verdict is `unsat` (NOT the valid verdict), so the integer
    // path declines; the genuine `unsat` comes from the other passes. It must
    // NOT be wrongly flipped to `sat` by the relaxation.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let zero = arena.int_const(0);
    let ten = arena.int_const(10);
    let ge0 = arena.int_ge(x, zero).unwrap();
    let le10 = arena.int_le(x, ten).unwrap();
    let body = arena.and(ge0, le10).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_not_sat(&mut arena, &[forall]);
}

#[test]
fn forall_int_gt0_single_atom_still_unsat() {
    // ∀x:Int. x > 0 — FALSE in every model (x = 0). Already decided `unsat` by
    // the single-atom unsat-∀ pass, which runs *before* the integer relaxation.
    // The relaxation must not interfere and must not make it `sat`.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let zero = arena.int_const(0);
    let body = arena.int_gt(x, zero).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_int_valid_then_extra_constraint_sat() {
    // ∀x:Int. (x ≤ 0 ∨ x > 0) rewrites to `true`; a separate satisfiable
    // assertion (y = 3) leaves the whole query SAT — confirming the rewrite
    // dispatches the residual correctly rather than short-circuiting.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let zero = arena.int_const(0);
    let le0 = arena.int_le(x, zero).unwrap();
    let gt0 = arena.int_gt(x, zero).unwrap();
    let body = arena.or(le0, gt0).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    let (_y_sym, y) = int(&mut arena, "y");
    let three = arena.int_const(3);
    let y_is_3 = arena.eq(y, three).unwrap();
    assert_sat(&mut arena, &[forall, y_is_3]);
}

#[test]
fn forall_int_valid_then_contradiction_unsat() {
    // ∀x:Int. (x ≤ 0 ∨ x > 0) rewrites to `true`; a contradictory companion
    // assertion (y = 3 ∧ y = 4 via two equalities) leaves the query UNSAT. The
    // `true`-rewrite must not mask the contradiction.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let zero = arena.int_const(0);
    let le0 = arena.int_le(x, zero).unwrap();
    let gt0 = arena.int_gt(x, zero).unwrap();
    let body = arena.or(le0, gt0).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    let (_y_sym, y) = int(&mut arena, "y");
    let three = arena.int_const(3);
    let four = arena.int_const(4);
    let y_is_3 = arena.eq(y, three).unwrap();
    let y_is_4 = arena.eq(y, four).unwrap();
    assert_unsat(&mut arena, &[forall, y_is_3, y_is_4]);
}
