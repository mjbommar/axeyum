//! Single-variable real Fourier-Motzkin elimination for a top-level universal.
//!
//! `∀x:Real. φ` over linear real atoms is decided exactly by eliminating `x`
//! from `¬φ` (`∀x. φ ⟺ ¬∃x. ¬φ`; real FM is exact). These tests pin the newly
//! decided multi-atom real universals *and* the soundness negatives: non-linear
//! and integer universals must decline, and no real universal may be
//! mis-decided (a valid one never `unsat`, a false one never `sat`).
#![cfg(feature = "full")]

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
        "expected unsat"
    );
}

fn assert_sat(arena: &mut TermArena, assertions: &[TermId]) {
    assert!(
        matches!(check(arena, assertions), CheckResult::Sat(_)),
        "expected sat"
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
        "unsound: an unsatisfiable universal was wrongly reported sat"
    );
}

fn real(arena: &mut TermArena, name: &str) -> (axeyum_ir::SymbolId, TermId) {
    let s = arena.declare(name, Sort::Real).unwrap();
    let v = arena.var(s);
    (s, v)
}

fn rzero(arena: &mut TermArena) -> TermId {
    arena.real_const(Rational::zero())
}

fn rconst(arena: &mut TermArena, n: i128) -> TermId {
    arena.real_const(Rational::integer(n))
}

// ---------------------------------------------------------------------------
// DECIDES — the multi-atom real universals the pass now handles.
// ---------------------------------------------------------------------------

#[test]
fn forall_real_ge0_and_le10_is_unsat() {
    // ∀x:Real. (x ≥ 0 ∧ x ≤ 10) — false (x = -1 falsifies it) ⇒ unsat.
    let mut arena = TermArena::new();
    let (x_sym, x) = real(&mut arena, "x");
    let zero = rzero(&mut arena);
    let ten = rconst(&mut arena, 10);
    let ge0 = arena.real_ge(x, zero).unwrap();
    let le10 = arena.real_le(x, ten).unwrap();
    let body = arena.and(ge0, le10).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_real_le0_or_gt0_is_valid_sat() {
    // ∀x:Real. (x ≤ 0 ∨ x > 0) — real trichotomy, valid ⇒ the assertion is sat.
    let mut arena = TermArena::new();
    let (x_sym, x) = real(&mut arena, "x");
    let zero = rzero(&mut arena);
    let le0 = arena.real_le(x, zero).unwrap();
    let gt0 = arena.real_gt(x, zero).unwrap();
    let body = arena.or(le0, gt0).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[forall]);
}

#[test]
fn forall_real_lt0_or_ge0_is_valid_sat() {
    // ∀x:Real. (x < 0 ∨ x ≥ 0) — valid ⇒ sat. (Strictness on the other side.)
    let mut arena = TermArena::new();
    let (x_sym, x) = real(&mut arena, "x");
    let zero = rzero(&mut arena);
    let lt0 = arena.real_lt(x, zero).unwrap();
    let ge0 = arena.real_ge(x, zero).unwrap();
    let body = arena.or(lt0, ge0).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[forall]);
}

#[test]
fn forall_real_lt0_or_gt0_is_false_unsat() {
    // ∀x:Real. (x < 0 ∨ x > 0) — FALSE at x = 0 (the hole). ⇒ unsat.
    // ¬φ = (x ≥ 0 ∧ x ≤ 0), FM join: 0 ≤ x ≤ 0 has the solution x = 0, so
    // ∃x.¬φ is valid ⇒ ∀x.φ is false.
    let mut arena = TermArena::new();
    let (x_sym, x) = real(&mut arena, "x");
    let zero = rzero(&mut arena);
    let lt0 = arena.real_lt(x, zero).unwrap();
    let gt0 = arena.real_gt(x, zero).unwrap();
    let body = arena.or(lt0, gt0).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_unsat(&mut arena, &[forall]);
}

#[test]
fn exists_y_forall_x_le_y_or_ge_y_is_sat() {
    // ∃y:Real. ∀x:Real. (x ≤ y ∨ x ≥ y) — the inner universal is valid for every
    // y (trichotomy), so any y witnesses ⇒ sat.
    let mut arena = TermArena::new();
    let (y_sym, _y) = real(&mut arena, "y");
    let (x_sym, x) = real(&mut arena, "x");
    let y = arena.var(y_sym);
    let le = arena.real_le(x, y).unwrap();
    let ge = arena.real_ge(x, y).unwrap();
    let body = arena.or(le, ge).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    let exists = arena.exists(y_sym, forall).unwrap();
    assert_sat(&mut arena, &[exists]);
}

#[test]
fn forall_real_le_y_and_ge_y_minus_1_is_unsat() {
    // ∀x:Real. (x ≤ y ∧ x ≥ y - 1) — false (x = y + 5 falsifies). Rewrites to a
    // y-constraint that is unsatisfiable as a closed universal ⇒ unsat.
    let mut arena = TermArena::new();
    let (y_sym, _y) = real(&mut arena, "y");
    let (x_sym, x) = real(&mut arena, "x");
    let y = arena.var(y_sym);
    let one = rconst(&mut arena, 1);
    let y_minus_1 = arena.real_sub(y, one).unwrap();
    let le_y = arena.real_le(x, y).unwrap();
    let ge = arena.real_ge(x, y_minus_1).unwrap();
    let body = arena.and(le_y, ge).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_real_rewrite_to_y_constraint_then_sat() {
    // ∀x:Real. (x < 0 ∨ x ≥ y) — the universal is valid iff y ≤ 0 (else the gap
    // 0 ≤ x < y is a counterexample). FM rewrites the universal to (y ≤ 0); with
    // the extra assertion `y = -3` the query is SAT.
    let mut arena = TermArena::new();
    let (y_sym, _y) = real(&mut arena, "y");
    let (x_sym, x) = real(&mut arena, "x");
    let y = arena.var(y_sym);
    let zero = rzero(&mut arena);
    let lt0 = arena.real_lt(x, zero).unwrap();
    let ge_y = arena.real_ge(x, y).unwrap();
    let body = arena.or(lt0, ge_y).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    // y = -3 ⇒ y ≤ 0 ⇒ the universal holds ⇒ sat.
    let neg3 = rconst(&mut arena, -3);
    let y_is_neg3 = arena.eq(y, neg3).unwrap();
    assert_sat(&mut arena, &[forall, y_is_neg3]);
}

#[test]
fn forall_real_rewrite_to_y_constraint_then_unsat() {
    // Same universal as above (valid iff y ≤ 0), but now assert y = 5 ⇒ the
    // universal is false ⇒ the conjunction is unsat.
    let mut arena = TermArena::new();
    let (y_sym, _y) = real(&mut arena, "y");
    let (x_sym, x) = real(&mut arena, "x");
    let y = arena.var(y_sym);
    let zero = rzero(&mut arena);
    let lt0 = arena.real_lt(x, zero).unwrap();
    let ge_y = arena.real_ge(x, y).unwrap();
    let body = arena.or(lt0, ge_y).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    let five = rconst(&mut arena, 5);
    let y_is_5 = arena.eq(y, five).unwrap();
    assert_unsat(&mut arena, &[forall, y_is_5]);
}

#[test]
fn forall_real_eq_band_is_unsat() {
    // ∀x:Real. (x = 0) — false (x = 1) ⇒ unsat. (Equality splits to x≥0 ∧ x≤0.)
    let mut arena = TermArena::new();
    let (x_sym, x) = real(&mut arena, "x");
    let zero = rzero(&mut arena);
    let body = arena.eq(x, zero).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_unsat(&mut arena, &[forall]);
}

// ---------------------------------------------------------------------------
// SOUNDNESS NEGATIVES — must never be wrongly decided.
// ---------------------------------------------------------------------------

#[test]
fn forall_real_x_squared_ge_0_not_unsat() {
    // ∀x:Real. x·x ≥ 0 — TRUE (non-negative square), but non-linear ⇒ our pass
    // declines. Whatever the NRA path concludes, it must NOT be a (bogus) unsat.
    let mut arena = TermArena::new();
    let (x_sym, x) = real(&mut arena, "x");
    let zero = rzero(&mut arena);
    let x_sq = arena.real_mul(x, x).unwrap();
    let body = arena.real_ge(x_sq, zero).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_not_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_real_x_squared_lt_0_not_sat() {
    // ∀x:Real. x·x < 0 — FALSE, non-linear ⇒ our pass declines. Must NOT be a
    // (bogus) sat from our pass mis-eliminating the non-linear term.
    let mut arena = TermArena::new();
    let (x_sym, x) = real(&mut arena, "x");
    let zero = rzero(&mut arena);
    let x_sq = arena.real_mul(x, x).unwrap();
    let body = arena.real_lt(x_sq, zero).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_not_sat(&mut arena, &[forall]);
}

#[test]
fn forall_int_band_not_misdecided_by_fm() {
    // ∀x:Int. (x ≥ 0 ∧ x ≤ 10) — FALSE (x = -1) ⇒ genuinely unsat. Int is out of
    // scope for the *real* FM pass; the verdict here is decided by other passes,
    // and it must be the correct one (unsat) — never a bogus sat from FM.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.int_const(0);
    let ten = arena.int_const(10);
    let ge0 = arena.int_ge(x, zero).unwrap();
    let le10 = arena.int_le(x, ten).unwrap();
    let body = arena.and(ge0, le10).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    // The real-FM pass must not touch it; the genuine truth is unsat.
    assert_not_sat(&mut arena, &[forall]);
}

#[test]
fn forall_real_valid_conjunction_not_unsat() {
    // ∀x:Real. (x ≤ x + 1 ∧ x + 2 ≥ x) — both atoms valid (x-free after cancel),
    // so the universal is valid ⇒ sat. Must NOT be wrongly unsat.
    let mut arena = TermArena::new();
    let (x_sym, x) = real(&mut arena, "x");
    let one = rconst(&mut arena, 1);
    let two = rconst(&mut arena, 2);
    let x_plus_1 = arena.real_add(x, one).unwrap();
    let x_plus_2 = arena.real_add(x, two).unwrap();
    let a1 = arena.real_le(x, x_plus_1).unwrap();
    let a2 = arena.real_ge(x_plus_2, x).unwrap();
    let body = arena.and(a1, a2).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_not_unsat(&mut arena, &[forall]);
}

#[test]
fn forall_real_genuinely_false_disjunction_not_sat() {
    // ∀x:Real. (x ≤ -1 ∨ x ≥ 1) — FALSE (x = 0 is in neither half). Must NOT be
    // wrongly sat. ¬φ = (x > -1 ∧ x < 1), FM: -1 < x < 1 has solutions ⇒ ∀ false.
    let mut arena = TermArena::new();
    let (x_sym, x) = real(&mut arena, "x");
    let neg1 = rconst(&mut arena, -1);
    let one = rconst(&mut arena, 1);
    let le = arena.real_le(x, neg1).unwrap();
    let ge = arena.real_ge(x, one).unwrap();
    let body = arena.or(le, ge).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_not_sat(&mut arena, &[forall]);
    // And concretely it should be unsat.
    let mut arena2 = TermArena::new();
    let (x_sym2, x2) = real(&mut arena2, "x");
    let neg1b = rconst(&mut arena2, -1);
    let oneb = rconst(&mut arena2, 1);
    let le2 = arena2.real_le(x2, neg1b).unwrap();
    let ge2 = arena2.real_ge(x2, oneb).unwrap();
    let body2 = arena2.or(le2, ge2).unwrap();
    let forall2 = arena2.forall(x_sym2, body2).unwrap();
    assert_unsat(&mut arena2, &[forall2]);
}

#[test]
fn forall_real_x_in_uf_declined_not_misdecided() {
    // ∀x:Real. (f(x) ≥ 0 ∧ x ≤ 10) — x inside an uninterpreted function is not
    // linear ⇒ decline. Must not be mis-decided to sat by FM ignoring `f(x)`.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let (x_sym, x) = real(&mut arena, "x");
    let zero = rzero(&mut arena);
    let ten = rconst(&mut arena, 10);
    let fx = arena.apply(f, &[x]).unwrap();
    let fx_ge0 = arena.real_ge(fx, zero).unwrap();
    let le10 = arena.real_le(x, ten).unwrap();
    let body = arena.and(fx_ge0, le10).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    // The universal is actually false (x = -1 with f(-1) ≥ 0 not forced), so it
    // must never be reported sat by our pass dropping the f(x) atom.
    assert_not_sat(&mut arena, &[forall]);
}
