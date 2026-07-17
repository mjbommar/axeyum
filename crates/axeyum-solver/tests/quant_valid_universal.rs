//! Valid-universal elimination (sat-side universal-closure validity check).
//!
//! A standalone *valid* universal `∀x. body` over `Int`/`Real`/an uninterpreted
//! sort is satisfiable (true in every model) but the infinite-domain
//! instantiation/MBQI fallback — which only ever concludes `unsat`/`unknown` —
//! never reached it. The valid-universal pass decides these `sat` by proving
//! `¬body[x := c]` UNSAT for a fresh constant `c`. These tests pin the newly
//! decided `sat` cases *and* confirm the strictly-additive guarantee: the
//! non-valid and UNSAT-by-instantiation cases are unaffected.
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
    assert!(matches!(check(arena, assertions), CheckResult::Sat(_)));
}

fn assert_unsat(arena: &mut TermArena, assertions: &[TermId]) {
    assert!(matches!(check(arena, assertions), CheckResult::Unsat));
}

#[test]
fn forall_int_x_plus_zero_eq_x_is_sat() {
    // ∀x:Int. x + 0 == x — valid (identity), so satisfiable.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.int_const(0);
    let sum = arena.int_add(x, zero).unwrap();
    let body = arena.eq(sum, x).unwrap();
    let all = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[all]);
}

#[test]
fn forall_int_x_times_zero_eq_zero_is_sat() {
    // ∀x:Int. x * 0 == 0 — valid, so satisfiable.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.int_const(0);
    let prod = arena.int_mul(x, zero).unwrap();
    let body = arena.eq(prod, zero).unwrap();
    let all = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[all]);
}

#[test]
fn forall_uf_reflexivity_is_sat() {
    // ∀x. f(x) == f(x) — valid by EUF reflexivity, no arithmetic.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let fx = arena.apply(f, &[x]).unwrap();
    let body = arena.eq(fx, fx).unwrap();
    let all = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[all]);
}

#[test]
fn forall_real_square_nonneg_is_sat() {
    // ∀x:Real. x * x >= 0 — valid (NRA sign rule), so satisfiable.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let sq = arena.real_mul(x, x).unwrap();
    let zero = arena.real_const(axeyum_ir::Rational::zero());
    let body = arena.real_ge(sq, zero).unwrap();
    let all = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[all]);
}

#[test]
fn forall_int_excluded_middle_is_sat() {
    // ∀x:Int. x >= 0 ∨ x < 0 — a tautology, so satisfiable.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.int_const(0);
    let ge = arena.int_ge(x, zero).unwrap();
    let lt = arena.int_lt(x, zero).unwrap();
    let body = arena.or(ge, lt).unwrap();
    let all = arena.forall(x_sym, body).unwrap();
    assert_sat(&mut arena, &[all]);
}

#[test]
fn non_valid_universal_with_witness_stays_unsat() {
    // ∀x:Int. f(x) == 0  together with  f(7) == 1  is UNSAT (instantiate x:=7).
    // The valid-universal pass must NOT prove the universal valid (it is not) and
    // must leave it for the instantiation path, which refutes it.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let fx = arena.apply(f, &[x]).unwrap();
    let zero = arena.int_const(0);
    let body = arena.eq(fx, zero).unwrap();
    let all = arena.forall(x_sym, body).unwrap();

    let seven = arena.int_const(7);
    let f7 = arena.apply(f, &[seven]).unwrap();
    let one = arena.int_const(1);
    let f7_is_1 = arena.eq(f7, one).unwrap();

    assert_unsat(&mut arena, &[all, f7_is_1]);
}

#[test]
fn unsat_by_instantiation_still_works() {
    // ∀x. f(x) == 0  with  f(a) == 1  is UNSAT (classic instantiation refutation).
    // Confirms the pass did not break the existing UNSAT-by-instantiation route.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let fx = arena.apply(f, &[x]).unwrap();
    let zero = arena.int_const(0);
    let body = arena.eq(fx, zero).unwrap();
    let all = arena.forall(x_sym, body).unwrap();

    let a_sym = arena.declare("a", Sort::Int).unwrap();
    let a = arena.var(a_sym);
    let fa = arena.apply(f, &[a]).unwrap();
    let one = arena.int_const(1);
    let fa_is_1 = arena.eq(fa, one).unwrap();

    assert_unsat(&mut arena, &[all, fa_is_1]);
}

#[test]
fn satisfiable_but_not_valid_universal_is_never_wrongly_decided() {
    // ∀x:Int. x <= g(x) (g uninterpreted) is satisfiable but NOT valid. The pass
    // cannot prove it valid, so it falls through to the existing path. Whatever
    // verdict results, it must never be wrongly `Unsat` (a soundness violation);
    // `Sat`/`Unknown` are both acceptable here.
    let mut arena = TermArena::new();
    let g = arena.declare_fun("g", &[Sort::Int], Sort::Int).unwrap();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let gx = arena.apply(g, &[x]).unwrap();
    let body = arena.int_le(x, gx).unwrap();
    let all = arena.forall(x_sym, body).unwrap();

    let result = check(&mut arena, &[all]);
    assert!(
        !matches!(result, CheckResult::Unsat),
        "must never wrongly refute"
    );
}

#[test]
fn nested_forall_int_add_comm_is_sat() {
    // ∀x.∀y. x + y == y + x — valid (LIA), but written as a NESTED universal, so
    // the validity pass must peel the whole `∀x.∀y.` prefix and substitute both
    // bound variables with fresh constants before the QF validity sub-check.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let y_sym = arena.declare("y", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let xy = arena.int_add(x, y).unwrap();
    let yx = arena.int_add(y, x).unwrap();
    let body = arena.eq(xy, yx).unwrap();
    let inner = arena.forall(y_sym, body).unwrap();
    let outer = arena.forall(x_sym, inner).unwrap();
    assert_sat(&mut arena, &[outer]);
}

#[test]
fn nested_forall_uf_reflexivity_is_sat() {
    // ∀x.∀y. (x == y) => (f(x) == f(y)) — valid by congruence, nested universals.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let y_sym = arena.declare("y", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let xy = arena.eq(x, y).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let fxy = arena.eq(fx, fy).unwrap();
    let body = arena.implies(xy, fxy).unwrap();
    let inner = arena.forall(y_sym, body).unwrap();
    let outer = arena.forall(x_sym, inner).unwrap();
    assert_sat(&mut arena, &[outer]);
}

#[test]
fn nested_forall_nonvalid_is_not_wrongly_decided() {
    // ∀x.∀y. x == y is NOT valid (false for x≠y); the pass must NOT prove it valid
    // (¬(cx==cy) is sat), and the query must never be wrongly Sat-by-validity. It
    // is genuinely unsatisfiable-as-an-assertion only if forced; here we just pin
    // that the validity pass does not mis-fire (result is not produced by a bogus
    // validity proof — never a wrong answer).
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let y_sym = arena.declare("y", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let body = arena.eq(x, y).unwrap();
    let inner = arena.forall(y_sym, body).unwrap();
    let outer = arena.forall(x_sym, inner).unwrap();
    // ∀x∀y. x=y is unsatisfiable (no model: pick x=0,y=1). The instantiation path
    // refutes it; crucially the validity pass must not have falsely proven it valid.
    let result = check(&mut arena, &[outer]);
    assert!(
        !matches!(result, CheckResult::Sat(_)),
        "∀x∀y. x=y must never be wrongly Sat, got {result:?}"
    );
}
