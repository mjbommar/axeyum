//! Exact decision of **closed** single-variable integer universals via the
//! integer-emptiness of the Fourier-Motzkin residual.
//!
//! A *closed* `∀x:Int. φ` (body mentions only the bound variable `x`) is decided
//! exactly: `∀x:Int. φ ⟺ ¬∃x:Int. ¬φ`, and `∃x:Int` of each DNF clause of `¬φ`
//! — a concrete real interval `(L, U)` — holds iff the interval contains an
//! integer (integer ceil/floor of the rational endpoints, with strictness). If
//! any clause contains an integer the universal is `unsat`; otherwise it rewrites
//! to `true` (`sat`).
//!
//! This *closes the inter-integer-gap* cases the real-validity relaxation
//! declines: `∀x:Int. (x ≤ 0 ∨ x ≥ 1)` is real-INVALID (the real hole `(0,1)`)
//! yet integer-VALID (no integer in `(0,1)`) ⇒ now decided `sat`.
//!
//! The suite also pins the SOUNDNESS NEGATIVES the closed path must NOT mis-
//! decide: an *open* integer universal (symbolic free variable) and a non-linear
//! universal must DECLINE the closed path, never reaching a bogus verdict.

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

fn int(arena: &mut TermArena, name: &str) -> (axeyum_ir::SymbolId, TermId) {
    let s = arena.declare(name, Sort::Int).unwrap();
    let v = arena.var(s);
    (s, v)
}

// ---------------------------------------------------------------------------
// DECIDES SAT — closed integer universals that are integer-valid.
// ---------------------------------------------------------------------------

#[test]
fn forall_int_le0_or_ge1_is_sat_gap() {
    // ∀x:Int. (x ≤ 0 ∨ x ≥ 1) — the integer-gap case. Real-INVALID (x = 0.5 is in
    // the real hole `(0,1)`) but integer-VALID (no integer in `(0,1)`). The closed
    // path decides this `sat` where the real-validity relaxation declines.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let le0 = arena.int_le(x, zero).unwrap();
    let ge1 = arena.int_ge(x, one).unwrap();
    let body = arena.or(le0, ge1).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[forall]);
}

#[test]
fn forall_int_lt0_or_ge1_unsat_zero_in_hole() {
    // ∀x:Int. (x < 0 ∨ x ≥ 1) — hole is the half-open `[0,1)`, which contains the
    // integer 0 ⇒ the universal is actually FALSE (x = 0 falsifies). Unsat.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let lt0 = arena.int_lt(x, zero).unwrap();
    let ge1 = arena.int_ge(x, one).unwrap();
    let body = arena.or(lt0, ge1).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_unsat(&mut arena, &[forall]);
}

// ---------------------------------------------------------------------------
// DECIDES UNSAT — closed integer universals that are integer-false.
// ---------------------------------------------------------------------------

#[test]
fn forall_int_le0_or_ge2_unsat_hole_holds_one() {
    // ∀x:Int. (x ≤ 0 ∨ x ≥ 2) — the open real hole is `(0,2)`, which DOES contain
    // an integer (x = 1). So `¬φ` has an integer ⇒ the universal is FALSE ⇒ unsat.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let zero = arena.int_const(0);
    let two = arena.int_const(2);
    let le0 = arena.int_le(x, zero).unwrap();
    let ge2 = arena.int_ge(x, two).unwrap();
    let body = arena.or(le0, ge2).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_int_lt0_or_gt0_unsat_x_eq_zero() {
    // ∀x:Int. (x < 0 ∨ x > 0) — the hole is the single point `{0}`, an integer ⇒
    // x = 0 falsifies the universal ⇒ unsat.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let zero = arena.int_const(0);
    let lt0 = arena.int_lt(x, zero).unwrap();
    let gt0 = arena.int_gt(x, zero).unwrap();
    let body = arena.or(lt0, gt0).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_int_ge0_unsat() {
    // ∀x:Int. x ≥ 0 — FALSE (x = -1). Single-atom; `¬φ` is `x < 0`, unbounded
    // below ⇒ contains integers ⇒ unsat. (Decided here or by the single-atom pass;
    // either way the verdict must be unsat.)
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let zero = arena.int_const(0);
    let body = arena.int_ge(x, zero).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_int_2x_le1_and_2x_ge1_is_sat_no_integer() {
    // ∀x:Int. ¬(2x ≤ 1 ∧ 2x ≥ 1) — body is the negation, i.e. (2x < 1 ∨ 2x > 1).
    // `¬body` is `2x ≤ 1 ∧ 2x ≥ 1`, i.e. `x = 1/2`, which has NO integer ⇒ the
    // universal is VALID ⇒ sat. Exercises a non-integer rational endpoint.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let two = arena.int_const(2);
    let one = arena.int_const(1);
    let two_x = arena.int_mul(two, x).unwrap();
    let le1 = arena.int_le(two_x, one).unwrap();
    let ge1 = arena.int_ge(two_x, one).unwrap();
    let conj = arena.and(le1, ge1).unwrap();
    let body = arena.not(conj).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[forall]);
}

#[test]
fn forall_int_2x_eq1_is_sat_no_integer() {
    // ∀x:Int. 2x ≠ 1 — `¬φ` is `2x = 1`, i.e. `x = 1/2`, NO integer ⇒ valid ⇒ sat.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let two = arena.int_const(2);
    let one = arena.int_const(1);
    let two_x = arena.int_mul(two, x).unwrap();
    let eq = arena.eq(two_x, one).unwrap();
    let body = arena.not(eq).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[forall]);
}

// ---------------------------------------------------------------------------
// COMPANION DISPATCH — the `true`-rewrite must not mask other assertions.
// ---------------------------------------------------------------------------

#[test]
fn forall_int_gap_then_extra_constraint_sat() {
    // ∀x:Int. (x ≤ 0 ∨ x ≥ 1) rewrites to `true`; a separate satisfiable
    // assertion (y = 3) leaves the whole query SAT.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let le0 = arena.int_le(x, zero).unwrap();
    let ge1 = arena.int_ge(x, one).unwrap();
    let body = arena.or(le0, ge1).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    let (_y_sym, y) = int(&mut arena, "y");
    let three = arena.int_const(3);
    let y_is_3 = arena.eq(y, three).unwrap();
    assert_sat(&mut arena, &[forall, y_is_3]);
}

#[test]
fn forall_int_gap_then_contradiction_unsat() {
    // ∀x:Int. (x ≤ 0 ∨ x ≥ 1) rewrites to `true`; a contradictory companion
    // (y = 3 ∧ y = 4) leaves the query UNSAT — the `true`-rewrite must not mask it.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let le0 = arena.int_le(x, zero).unwrap();
    let ge1 = arena.int_ge(x, one).unwrap();
    let body = arena.or(le0, ge1).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    let (_y_sym, y) = int(&mut arena, "y");
    let three = arena.int_const(3);
    let four = arena.int_const(4);
    let y_is_3 = arena.eq(y, three).unwrap();
    let y_is_4 = arena.eq(y, four).unwrap();
    assert_unsat(&mut arena, &[forall, y_is_3, y_is_4]);
}

// ---------------------------------------------------------------------------
// SOUNDNESS NEGATIVES — the closed path must DECLINE these (open / non-linear).
// ---------------------------------------------------------------------------

// NOTE: the *disjunctive* open universal `∀x:Int. (x ≤ y ∨ x ≥ y + 1)` (free
// `y`) is the symbolic twin of the gap case and the closed path correctly
// DECLINES it (symbolic bounds). But once declined it falls through to the
// general quantifier search, which does not terminate quickly on this shape —
// so the decline is pinned *directly* as a unit test on
// `eliminate_int_universal_closed` (it returns `None`) in the source module,
// rather than via a slow end-to-end `solve`. The end-to-end soundness of the
// decline is still covered by the fast single-atom open negative below.

#[test]
fn forall_int_open_symbolic_false_not_missat() {
    // ∀x:Int. x ≤ y with a FREE integer `y` — an OPEN universal, FALSE (x = y + 1
    // falsifies for any y). The closed path declines (symbolic bound); the verdict
    // must NOT be a bogus `sat`.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let (_y_sym, y) = int(&mut arena, "y");
    let body = arena.int_le(x, y).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_not_sat(&mut arena, &[forall]);
}

#[test]
fn forall_int_nonlinear_declined() {
    // ∀x:Int. x * x ≥ 0 — non-linear (`x·x`); the affine collector declines, so
    // the closed path declines. It is genuinely TRUE (squares are non-negative),
    // so it must NOT be a bogus `unsat`.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let zero = arena.int_const(0);
    let x_sq = arena.int_mul(x, x).unwrap();
    let body = arena.int_ge(x_sq, zero).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_not_unsat(&mut arena, &[forall]);
}
