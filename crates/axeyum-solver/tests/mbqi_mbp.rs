//! MBP-driven model-based quantifier instantiation (gap-analysis Gap 9).
//!
//! The MBQI refutation loop in `auto.rs` probes a fixed set of *scalar* candidate
//! values (the model's values, the body's `x`-free subterm evaluations, and their
//! `±1` neighbours) to falsify a universal `∀x. body` at the current model. That
//! probe is **incomplete**: a universal violated only at a witness *symbolic in
//! another variable*, and farther than `±1` from every probed scalar, is missed.
//!
//! These tests pin the cases the new MBP step closes. Each one is constructed so
//! that:
//!
//! - the earlier Fourier–Motzkin / open-gap universal paths DECLINE (the relevant
//!   bound has a non-unit coefficient on `x`, outside their integer-valued /
//!   constant-width fragment), so the query actually reaches MBQI; and
//! - the scalar probe's candidate set (built from the model's small values and
//!   their `±1` neighbours) does **not** contain a falsifying `x`, while the
//!   model-based projection of `∃x. ¬body` does synthesize one.
//!
//! Soundness is the anchor: every synthesized instance `body[x := t]` is a logical
//! consequence of `∀x. body`, so the augmented refutation transfers; the loop can
//! only ever add coverage, never a wrong `sat`/`unsat`. The suite therefore also
//! pins the soundness negatives (a genuinely valid universal must NOT become a
//! bogus `unsat`; a satisfiable quantified query must stay non-`unsat`).

use std::time::Duration;

use axeyum_ir::{Rational, Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(60))
}

fn check(arena: &mut TermArena, assertions: &[TermId]) -> CheckResult {
    solve(arena, assertions, &config()).expect("solve decides or returns unknown without error")
}

fn assert_unsat(arena: &mut TermArena, assertions: &[TermId]) {
    assert!(
        matches!(check(arena, assertions), CheckResult::Unsat),
        "expected unsat (the universal is false in every model of the ground constraints)"
    );
}

fn assert_not_unsat(arena: &mut TermArena, assertions: &[TermId]) {
    // Soundness negative: must NOT be a bogus `unsat`. Sat or unknown are fine.
    assert!(
        !matches!(check(arena, assertions), CheckResult::Unsat),
        "unsound: a satisfiable / undecidable query was wrongly reported unsat"
    );
}

fn assert_not_sat(arena: &mut TermArena, assertions: &[TermId]) {
    // Soundness negative: must NOT be a bogus `sat`.
    assert!(
        !matches!(check(arena, assertions), CheckResult::Sat(_)),
        "unsound: an unsatisfiable query was wrongly reported sat"
    );
}

fn int(arena: &mut TermArena, name: &str) -> (SymbolId, TermId) {
    let s = arena.declare(name, Sort::Int).unwrap();
    let v = arena.var(s);
    (s, v)
}

fn real(arena: &mut TermArena, name: &str) -> (SymbolId, TermId) {
    let s = arena.declare(name, Sort::Real).unwrap();
    let v = arena.var(s);
    (s, v)
}

// ---------------------------------------------------------------------------
// LIA — newly-decided UNSAT whose witness is symbolic in another variable and
// far from the scalar probe's `±1` neighbourhood.
// ---------------------------------------------------------------------------

#[test]
fn lia_coeff_witness_far_from_scalar_probe_is_unsat() {
    // ∀x:Int. (5·x ≤ y ∨ 5·x ≥ y + 6)  ∧  y = 100.
    //
    // ¬body = (5x > y ∧ 5x < y + 6). With y = 100 the band is 100 < 5x < 106, so
    // 5x = 105, x = 21 violates the universal. The whole query is therefore unsat.
    //
    // The non-unit coefficient `5` keeps it out of the constant-width / integer-
    // valued-endpoint open-gap fragment, so the FM paths decline and the query
    // reaches MBQI. The scalar probe's candidates are built from {y = 100,
    // y + 6 = 106, 0, 1, -1} and their `±1` neighbours — none is the witness
    // x = 21, and probing each as `x` makes `5x ≥ y` true, so the scalar probe
    // finds NO refinement. MBP's sub-solve of `100 < 5x < 106 ∧ y = 100` yields
    // x = 21, and `body[x := 21]` = `105 ≤ 100 ∨ 105 ≥ 106` = false blocks the
    // model ⇒ unsat.
    let mut arena = TermArena::new();
    let (y_sym, y) = int(&mut arena, "y");
    let (x_sym, x) = int(&mut arena, "x");
    let five = arena.int_const(5);
    let six = arena.int_const(6);
    let five_x = arena.int_mul(five, x).unwrap();
    let y_plus_6 = arena.int_add(y, six).unwrap();
    let le = arena.int_le(five_x, y).unwrap();
    let ge = arena.int_ge(five_x, y_plus_6).unwrap();
    let body = arena.or(le, ge).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();

    let hundred = arena.int_const(100);
    let y_var = arena.var(y_sym);
    let y_is_100 = arena.eq(y_var, hundred).unwrap();

    assert_unsat(&mut arena, &[forall, y_is_100]);
}

// ---------------------------------------------------------------------------
// LRA — the real analogue (strict-bound gap, non-unit coefficient).
// ---------------------------------------------------------------------------

#[test]
fn lra_coeff_witness_far_from_scalar_probe_is_unsat() {
    // ∀r:Real. (5·r ≤ y ∨ 5·r ≥ y + 3)  ∧  y = 100.
    //
    // ¬body = (5r > y ∧ 5r < y + 3). With y = 100 the band is 100 < 5r < 103, i.e.
    // 20 < r < 20.6 — non-empty, so some r violates the universal ⇒ unsat. The
    // witness band sits near r ≈ 20.x, far from every scalar candidate (built from
    // {100, 103, 0, ±1} and `±1` neighbours), so the scalar probe misses it; MBP's
    // `mbp_lra` projects the band and the sub-solve supplies a concrete witness.
    let mut arena = TermArena::new();
    let (y_sym, y) = real(&mut arena, "y");
    let (r_sym, r) = real(&mut arena, "r");
    let five = arena.real_const(Rational::integer(5));
    let three = arena.real_const(Rational::integer(3));
    let five_r = arena.real_mul(five, r).unwrap();
    let y_plus_3 = arena.real_add(y, three).unwrap();
    let le = arena.real_le(five_r, y).unwrap();
    let ge = arena.real_ge(five_r, y_plus_3).unwrap();
    let body = arena.or(le, ge).unwrap();
    let forall = arena.forall(r_sym, body).unwrap();

    let hundred = arena.real_const(Rational::integer(100));
    let y_var = arena.var(y_sym);
    let y_is_100 = arena.eq(y_var, hundred).unwrap();

    assert_unsat(&mut arena, &[forall, y_is_100]);
}

// ---------------------------------------------------------------------------
// DECLINE / no-regression — a genuinely VALID universal must NOT become a bogus
// `unsat`: the MBP sub-solve of `∃x. ¬body` is unsat, so the helper declines.
// ---------------------------------------------------------------------------

#[test]
fn lia_valid_universal_is_not_misdecided_unsat() {
    // ∀x:Int. (5·x ≤ y ∨ 5·x ≥ y - 6)  ∧  y = 100.
    //
    // The two clauses jointly cover ALL integers (`5x ≥ y - 6` already holds for
    // every x with `5x ≥ y` and far below), so the universal is valid — there is
    // NO witness. `¬body = (5x > y ∧ 5x < y - 6)` is unsat (empty band), the MBP
    // sub-solve declines, and the query must NOT be reported unsat.
    let mut arena = TermArena::new();
    let (y_sym, y) = int(&mut arena, "y");
    let (x_sym, x) = int(&mut arena, "x");
    let five = arena.int_const(5);
    let six = arena.int_const(6);
    let five_x = arena.int_mul(five, x).unwrap();
    let y_minus_6 = arena.int_sub(y, six).unwrap();
    let le = arena.int_le(five_x, y).unwrap();
    let ge = arena.int_ge(five_x, y_minus_6).unwrap();
    let body = arena.or(le, ge).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();

    let hundred = arena.int_const(100);
    let y_var = arena.var(y_sym);
    let y_is_100 = arena.eq(y_var, hundred).unwrap();

    assert_not_unsat(&mut arena, &[forall, y_is_100]);
}

// ---------------------------------------------------------------------------
// SOUNDNESS — an existing satisfiable quantified query stays non-`unsat`.
// ---------------------------------------------------------------------------

#[test]
fn satisfiable_quantified_query_stays_non_unsat() {
    // ∀x:Int. x + x = 2·x is valid (a tautology); a companion `w = 7` is
    // satisfiable, so the whole query is satisfiable and must never be `unsat`.
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let two = arena.int_const(2);
    let x_plus_x = arena.int_add(x, x).unwrap();
    let two_x = arena.int_mul(two, x).unwrap();
    let body = arena.eq(x_plus_x, two_x).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();

    let (_w_sym, w) = int(&mut arena, "w");
    let seven = arena.int_const(7);
    let w_is_7 = arena.eq(w, seven).unwrap();

    assert_not_unsat(&mut arena, &[forall, w_is_7]);
    // And it must not be wrongly reported `unsat` even on its own.
    assert_not_unsat(&mut arena, &[forall]);
}

#[test]
fn unsatisfiable_ground_companion_stays_non_sat() {
    // A trivially unsatisfiable ground constraint alongside a valid universal must
    // never be reported `sat` (guards the additive MBP step against masking).
    let mut arena = TermArena::new();
    let (x_sym, x) = int(&mut arena, "x");
    let two = arena.int_const(2);
    let x_plus_x = arena.int_add(x, x).unwrap();
    let two_x = arena.int_mul(two, x).unwrap();
    let body = arena.eq(x_plus_x, two_x).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();

    let (_w_sym, w) = int(&mut arena, "w");
    let three = arena.int_const(3);
    let four = arena.int_const(4);
    let w_is_3 = arena.eq(w, three).unwrap();
    let w_is_4 = arena.eq(w, four).unwrap();

    assert_not_sat(&mut arena, &[forall, w_is_3, w_is_4]);
}
