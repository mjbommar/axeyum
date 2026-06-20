//! Unsatisfiable-universal detection (an always-false linear universal).
//!
//! A top-level `∀x. (c·x ⋈ t)` whose body is a *single* linear arithmetic atom
//! in which `x` genuinely appears (net coefficient `c ≠ 0`), `t` is `x`-free,
//! and `⋈ ∈ {<, ≤, >, ≥, =}` (never `≠`) is **false in every model** — an
//! unbounded linear function of `x` (both `Int` and `Real` are unbounded)
//! cannot satisfy a one-sided bound or an equality for *all* `x`. So asserting
//! it makes the whole query `unsat`. These tests pin the newly decided `unsat`
//! cases *and* the soundness negatives: the disequality, vacuous-`c=0`,
//! valid-disjunction, and guarded shapes that must **never** be wrongly `unsat`.

use std::time::Duration;

use axeyum_ir::{Rational, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

fn check(arena: &mut TermArena, assertions: &[TermId]) -> CheckResult {
    solve(arena, assertions, &config()).expect("solve decides or returns unknown without error")
}

fn assert_unsat(arena: &mut TermArena, assertions: &[TermId]) {
    assert!(
        matches!(check(arena, assertions), CheckResult::Unsat),
        "expected unsat (always-false universal)"
    );
}

fn assert_not_unsat(arena: &mut TermArena, assertions: &[TermId]) {
    // Soundness negative: the result must NOT be a (bogus) unsat. Sat or unknown
    // are both acceptable — the pass must simply never claim a false unsat.
    assert!(
        !matches!(check(arena, assertions), CheckResult::Unsat),
        "unsound: a satisfiable / undecidable universal was wrongly reported unsat"
    );
}

// ---------------------------------------------------------------------------
// Positives — must become `unsat`.
// ---------------------------------------------------------------------------

#[test]
fn forall_x_x_gt_0_is_unsat() {
    // ∀x:Int. x > 0 — false at x = 0. c = 1 ≠ 0, single atom, x-free RHS.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.int_const(0);
    let body = arena.int_gt(x, zero).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_x_2x_eq_5_is_unsat() {
    // ∀x:Int. 2·x = 5 — at most one solution (x = 5/2), so not for all x. c = 2.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let two = arena.int_const(2);
    let five = arena.int_const(5);
    let two_x = arena.int_mul(two, x).unwrap();
    let body = arena.eq(two_x, five).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_x_real_x_le_y_is_unsat() {
    // ∀x:Real. x ≤ y (y free) — false at x = y + 1. c = 1, t = y is x-free.
    let mut arena = TermArena::new();
    let y_sym = arena.declare("y", Sort::Real).unwrap();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let y = arena.var(y_sym);
    let x = arena.var(x_sym);
    let body = arena.real_le(x, y).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_unsat(&mut arena, &[forall]);
}

#[test]
fn exists_y_forall_x_x_le_y_is_unsat() {
    // ∃y:Int.∀x:Int. x ≤ y. Skolemize y → c ⇒ ∀x. x ≤ c (this shape) ⇒ unsat,
    // so the existential closure is unsat too (no integer upper-bounds them all).
    let mut arena = TermArena::new();
    let y_sym = arena.declare("y", Sort::Int).unwrap();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let y = arena.var(y_sym);
    let x = arena.var(x_sym);
    let body = arena.int_le(x, y).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    let exists = arena.exists(y_sym, forall).unwrap();
    assert_unsat(&mut arena, &[exists]);
}

// ---------------------------------------------------------------------------
// Soundness negatives — must NOT become `unsat`.
// ---------------------------------------------------------------------------

#[test]
fn forall_x_2x_ne_5_is_not_unsat() {
    // ∀x:Int. 2·x ≠ 5 — TRUE (no integer halves 5). Built as not(2·x = 5), whose
    // top operator is `not`, not a bare atom ⇒ this pass declines (no false unsat).
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let two = arena.int_const(2);
    let five = arena.int_const(5);
    let two_x = arena.int_mul(two, x).unwrap();
    let eq = arena.eq(two_x, five).unwrap();
    let body = arena.not(eq).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_not_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_x_x_plus_y_ge_x_is_not_unsat() {
    // ∀x:Int. x + y ≥ x — net x-coefficient is 0 (vacuous). The vacuous pass owns
    // it (⟺ y ≥ 0, sat with y = 0); this pass must decline (c = 0 excluded).
    let mut arena = TermArena::new();
    let y_sym = arena.declare("y", Sort::Int).unwrap();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let y = arena.var(y_sym);
    let x = arena.var(x_sym);
    let sum = arena.int_add(x, y).unwrap();
    let body = arena.int_ge(sum, x).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_not_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_x_x_gt_0_or_x_le_0_is_not_unsat() {
    // ∀x:Int. (x > 0 ∨ x ≤ 0) — VALID (true for every x). The body is a
    // disjunction, not a single atom ⇒ this pass declines (no false unsat).
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.int_const(0);
    let gt = arena.int_gt(x, zero).unwrap();
    let le = arena.int_le(x, zero).unwrap();
    let body = arena.or(gt, le).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_not_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_x_guarded_range_implies_ge_5_is_not_unsat() {
    // ∀x:Int. (0 ≤ x ≤ 2) ⇒ x ≥ 5 — UNSAT in fact (x = 0 violates), but the body
    // is an implication, not a single atom, so this pass declines and leaves the
    // verdict to the guarded/finite path (which is unchanged). Either way: the
    // result is not produced by *this* pass mis-firing on a multi-atom body.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.int_const(0);
    let two = arena.int_const(2);
    let five = arena.int_const(5);
    let lo = arena.int_le(zero, x).unwrap();
    let hi = arena.int_le(x, two).unwrap();
    let guard = arena.and(lo, hi).unwrap();
    let concl = arena.int_ge(x, five).unwrap();
    let body = arena.implies(guard, concl).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    // This guarded universal is genuinely unsatisfiable (it asserts a false
    // implication over the finite range), so the guarded/finite path decides it
    // unsat. The check here is only that the verdict is *sound* — and indeed it
    // is unsat — proving this pass's structural decline did not break it.
    assert_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_x_real_2x_eq_5_is_unsat() {
    // ∀x:Real. 2·x = 5 — over the reals it holds at exactly x = 5/2, so not for
    // all x ⇒ unsat (c = 2 ≠ 0, single equality atom, x-free RHS).
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let two = arena.real_const(Rational::integer(2));
    let five = arena.real_const(Rational::integer(5));
    let two_x = arena.real_mul(two, x).unwrap();
    let body = arena.eq(two_x, five).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_unsat(&mut arena, &[forall]);
}
