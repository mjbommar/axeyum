//! Vacuous-universal elimination (bound variable that does not affect the body).
//!
//! A top-level `∀x. body` (quantifier-free body) in which the bound variable `x`
//! is *truth-irrelevant* — every arithmetic atom mentioning `x` has net
//! `x`-coefficient `0` after linear normalization, and `x` appears nowhere else —
//! is logically equivalent to `body[x := 0]`. The vacuous-universal pass decides
//! these (notably the residual `∀x. x + c >= x` ⟺ `c >= 0` that skolemizing
//! `∃y.∀x. x + y >= x` leaves), which neither the finite-domain expansion nor the
//! *valid*-universal pass reaches. These tests pin the newly decided `sat` cases
//! *and* the strictly-additive guarantee: a genuinely `x`-dependent universal is
//! never wrongly decided.

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
        "expected sat"
    );
}

fn assert_not_sat(arena: &mut TermArena, assertions: &[TermId]) {
    // Soundness negative: the result must NOT be a (bogus) sat. Unsat or unknown
    // are both acceptable — the pass must simply never claim a false sat.
    assert!(
        !matches!(check(arena, assertions), CheckResult::Sat(_)),
        "unsound: a genuinely x-dependent universal was wrongly reported sat"
    );
}

#[test]
fn exists_y_forall_x_x_plus_y_ge_x_is_sat() {
    // ∃y.∀x. x + y >= x. Skolemize y→c ⇒ ∀x. x + c >= x ⟺ c >= 0 (x vacuous).
    // Witness y = 0 ⇒ sat.
    let mut arena = TermArena::new();
    let y_sym = arena.declare("y", Sort::Int).unwrap();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let y = arena.var(y_sym);
    let x = arena.var(x_sym);
    let sum = arena.int_add(x, y).unwrap();
    let body = arena.int_ge(sum, x).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    let exists = arena.exists(y_sym, forall).unwrap();
    assert_sat(&mut arena, &[exists]);
}

#[test]
fn forall_x_x_plus_y_ge_x_standalone_is_sat() {
    // ∀x. x + y >= x with `y` free ⟺ y >= 0; a model with y = 0 exists ⇒ sat.
    let mut arena = TermArena::new();
    let y_sym = arena.declare("y", Sort::Int).unwrap();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let y = arena.var(y_sym);
    let x = arena.var(x_sym);
    let sum = arena.int_add(x, y).unwrap();
    let body = arena.int_ge(sum, x).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[forall]);
}

#[test]
fn forall_x_x_times_zero_plus_y_eq_y_is_sat() {
    // ∀x. x*0 + y == y — x's coefficient is 0 (x*0 cancels) ⇒ vacuous, valid ⇒ sat.
    let mut arena = TermArena::new();
    let y_sym = arena.declare("y", Sort::Int).unwrap();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let y = arena.var(y_sym);
    let x = arena.var(x_sym);
    let zero = arena.int_const(0);
    let x0 = arena.int_mul(x, zero).unwrap();
    let lhs = arena.int_add(x0, y).unwrap();
    let body = arena.eq(lhs, y).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[forall]);
}

#[test]
fn forall_real_x_x_plus_c_ge_x_is_sat() {
    // ∀x:Real. x + c >= x ⟺ c >= 0; with `c` free a model c = 0 exists ⇒ sat.
    let mut arena = TermArena::new();
    let c_sym = arena.declare("c", Sort::Real).unwrap();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let c = arena.var(c_sym);
    let x = arena.var(x_sym);
    let sum = arena.real_add(x, c).unwrap();
    let body = arena.real_ge(sum, x).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[forall]);
}

// --- soundness negatives: genuinely x-dependent universals -------------------

#[test]
fn exists_y_forall_x_x_le_y_is_not_wrongly_sat() {
    // ∃y.∀x. x <= y. Skolemize y→c ⇒ ∀x. x <= c, which is FALSE (no integer upper
    // bounds every integer). `x` is x-DEPENDENT (coefficient 1), so the vacuous
    // pass must leave it untouched — the result must NOT be a bogus sat.
    let mut arena = TermArena::new();
    let y_sym = arena.declare("y", Sort::Int).unwrap();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let y = arena.var(y_sym);
    let x = arena.var(x_sym);
    let body = arena.int_le(x, y).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    let exists = arena.exists(y_sym, forall).unwrap();
    assert_not_sat(&mut arena, &[exists]);
}

#[test]
fn forall_x_x_ge_zero_is_not_wrongly_sat() {
    // ∀x:Int. x >= 0 is FALSE (x = -1 falsifies it). `x` is x-dependent, so the
    // pass must not drop it; the correct verdict is never sat.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.int_const(0);
    let body = arena.int_ge(x, zero).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_not_sat(&mut arena, &[forall]);
}

#[test]
fn forall_x_mixed_dependent_atom_is_not_wrongly_sat() {
    // ∀x. (x + c >= x) ∧ (x >= 0): the first conjunct is x-vacuous but the second
    // is x-DEPENDENT, so the whole body is not vacuous. The pass must leave it
    // untouched; the universal is false (x = -1), so never a bogus sat.
    let mut arena = TermArena::new();
    let c_sym = arena.declare("c", Sort::Int).unwrap();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let c = arena.var(c_sym);
    let x = arena.var(x_sym);
    let zero = arena.int_const(0);
    let sum = arena.int_add(x, c).unwrap();
    let vacuous_atom = arena.int_ge(sum, x).unwrap();
    let dep_atom = arena.int_ge(x, zero).unwrap();
    let body = arena.and(vacuous_atom, dep_atom).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_not_sat(&mut arena, &[forall]);
}

#[test]
fn forall_x_uf_argument_is_left_untouched() {
    // ∀x. f(x) == f(x) — x appears inside a UF argument. The vacuous pass must NOT
    // treat this as a linear-arithmetic atom (it bails on the UF occurrence); the
    // valid-universal pass still decides it sat by EUF reflexivity. This pins that
    // the vacuous pass does not interfere with that route.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let fx = arena.apply(f, &[x]).unwrap();
    let body = arena.eq(fx, fx).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[forall]);
}
