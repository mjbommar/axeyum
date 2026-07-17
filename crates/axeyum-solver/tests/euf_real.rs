//! EUF over the reals (`QF_UFLRA`): a real-sorted uninterpreted-function application
//! must route through the EUF + linear-arithmetic combination, not error out on the
//! pure-real linearizer. Previously a real `f(x)` returned a hard
//! `Err Unsupported("QF_LRA: non-linear or non-real subterm ...")`; the dispatch now
//! falls through to `check_with_uf_arithmetic` (mirroring the integer EUF+LIA path),
//! so these decide — and crucially never return an `Err`.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Rational, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

fn real(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, Sort::Real).unwrap();
    arena.var(s)
}

#[test]
fn real_uf_application_does_not_error() {
    // f(x) == 1.0 — satisfiable (f maps x to 1). The PRIMARY guarantee (gap G1, the
    // "unknown is never an error" rule) is that this must NOT be a hard `Err`. The
    // QF_UFLRA *sat-model projection* for an arithmetic-sorted UF is not yet built,
    // so `Unknown` is the current best-effort result; `Sat` would also be acceptable
    // once projection lands. The forbidden outcome is `Err` (or `Unsat`).
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let x = real(&mut arena, "x");
    let fx = arena.apply(f, &[x]).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let e = arena.eq(fx, one).unwrap();

    let result = solve(&mut arena, &[e], &config()).expect("must NOT error on real UF (gap G1)");
    assert!(
        matches!(result, CheckResult::Sat(_) | CheckResult::Unknown(_)),
        "f(x) == 1.0 must be Sat or graceful Unknown (never Err/Unsat), got {result:?}"
    );
}

#[test]
fn real_uf_congruence_conflict_is_unsat() {
    // f(x) == 1 ∧ f(y) == 2 ∧ x == y — UNSAT by congruence over the real UF f:
    // x = y ⇒ f(x) = f(y), contradicting 1 ≠ 2.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let two = arena.real_const(Rational::integer(2));
    let e1 = arena.eq(fx, one).unwrap();
    let e2 = arena.eq(fy, two).unwrap();
    let e3 = arena.eq(x, y).unwrap();

    let result =
        solve(&mut arena, &[e1, e2, e3], &config()).expect("must not error on real UF congruence");
    assert!(
        matches!(result, CheckResult::Unsat),
        "f(x)=1 ∧ f(y)=2 ∧ x=y must be Unsat (congruence), got {result:?}"
    );
}

#[test]
fn real_uf_arithmetic_combination_is_unsat() {
    // f(a) ≤ b ∧ b ≤ f(a) ∧ a == c ∧ ¬(f(c) == b) — the classic Nelson-Oppen case
    // over reals: f(a)=b (squeeze) and a=c ⇒ f(c)=f(a)=b, contradicting f(c) ≠ b.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let a = real(&mut arena, "a");
    let b = real(&mut arena, "b");
    let c = real(&mut arena, "c");
    let fa = arena.apply(f, &[a]).unwrap();
    let fc = arena.apply(f, &[c]).unwrap();
    let le1 = arena.real_le(fa, b).unwrap();
    let le2 = arena.real_le(b, fa).unwrap();
    let ac = arena.eq(a, c).unwrap();
    let fc_eq_b = arena.eq(fc, b).unwrap();
    let ne = arena.not(fc_eq_b).unwrap();

    let result = solve(&mut arena, &[le1, le2, ac, ne], &config())
        .expect("must not error on real UF + arithmetic");
    assert!(
        matches!(result, CheckResult::Unsat),
        "f(a)≤b ∧ b≤f(a) ∧ a=c ∧ f(c)≠b must be Unsat, got {result:?}"
    );
}
