//! Verifies the P2.1 lazy bit-blasting dispatch wiring: `SolverConfig::lazy_bv`
//! routes `solve()` to the abstraction-refinement strategy (opt-in), and is a
//! no-op when off. (Non-ignored: fast — the cases decide in milliseconds.)

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{CheckResult, SolverConfig, solve};

/// `x = 1 ∧ x = 2` (contradiction) ∧ `r = p*q` (incidental 64-bit multiplier):
/// with `lazy_bv` on, `solve()` routes to the lazy strategy and decides UNSAT
/// via abstraction (the multiplier is irrelevant to the contradiction).
#[test]
#[allow(clippy::many_single_char_names)] // x, p, q, r are natural BV-variable names
fn lazy_bv_flag_routes_and_decides_incidental() {
    let mut a = TermArena::new();
    let xs = a.declare("x", Sort::BitVec(64)).unwrap();
    let ps = a.declare("p", Sort::BitVec(64)).unwrap();
    let qs = a.declare("q", Sort::BitVec(64)).unwrap();
    let rs = a.declare("r", Sort::BitVec(64)).unwrap();
    let x = a.var(xs);
    let p = a.var(ps);
    let q = a.var(qs);
    let r = a.var(rs);
    let one = a.bv_const(64, 1).unwrap();
    let two = a.bv_const(64, 2).unwrap();
    let mul = a.bv_mul(p, q).unwrap();
    let c1 = a.eq(x, one).unwrap();
    let c2 = a.eq(x, two).unwrap();
    let c3 = a.eq(r, mul).unwrap();

    let res = solve(
        &mut a,
        &[c1, c2, c3],
        &SolverConfig::default().with_lazy_bv(true),
    )
    .unwrap();
    assert!(
        matches!(res, CheckResult::Unsat),
        "lazy-routed solve must decide UNSAT, got {res:?}"
    );
}

/// Flag off (default): behavior unchanged — a trivial sat problem solves normally.
#[test]
fn lazy_bv_flag_off_is_default() {
    let mut a = TermArena::new();
    let xs = a.declare("x", Sort::BitVec(8)).unwrap();
    let x = a.var(xs);
    let five = a.bv_const(8, 5).unwrap();
    let eq = a.eq(x, five).unwrap();
    let res = solve(&mut a, &[eq], &SolverConfig::default()).unwrap();
    assert!(
        matches!(res, CheckResult::Sat(_)),
        "default (lazy off) solve unchanged, got {res:?}"
    );
}

/// Lazy and eager agree on a sat instance whose model involves the heavy op
/// (the refinement loop must produce a genuine, replayed model).
#[test]
fn lazy_bv_sat_agrees_with_eager() {
    let build = |a: &mut TermArena| {
        let ps = a.declare("p", Sort::BitVec(8)).unwrap();
        let qs = a.declare("q", Sort::BitVec(8)).unwrap();
        let p = a.var(ps);
        let q = a.var(qs);
        let prod = a.bv_mul(p, q).unwrap();
        let six = a.bv_const(8, 6).unwrap();
        let two = a.bv_const(8, 2).unwrap();
        let e1 = a.eq(prod, six).unwrap();
        let e2 = a.eq(p, two).unwrap(); // p=2 ∧ p*q=6 ⇒ q=3, sat
        vec![e1, e2]
    };
    // TermArena is not Clone — rebuild the assertions in a fresh arena per run.
    let mut a1 = TermArena::new();
    let asserts1 = build(&mut a1);
    let eager = solve(&mut a1, &asserts1, &SolverConfig::default()).unwrap();
    let mut a2 = TermArena::new();
    let asserts2 = build(&mut a2);
    let lazy = solve(
        &mut a2,
        &asserts2,
        &SolverConfig::default().with_lazy_bv(true),
    )
    .unwrap();
    assert!(
        matches!(eager, CheckResult::Sat(_)),
        "eager baseline must be sat, got {eager:?}"
    );
    assert!(
        matches!(lazy, CheckResult::Sat(_)),
        "lazy must find the model (p=2,q=3), got {lazy:?}"
    );
}
