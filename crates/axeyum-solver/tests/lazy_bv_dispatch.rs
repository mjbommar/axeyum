//! Verifies the P2.1 lazy bit-blasting dispatch wiring: `SolverConfig::lazy_bv`
//! routes `solve()` to the abstraction-refinement strategy (opt-in), and is a
//! no-op when off. (Non-ignored: fast — the cases decide in milliseconds.)
#![cfg(feature = "full")]

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{
    CheckResult, LazyBvBackend, SolverBackend, SolverConfig, check_lazy_bv_abstraction_ro, solve,
};

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
    // Rebuild the assertions in a fresh arena per run (distinct `&mut` borrows).
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

/// The read-only entry point decides correctly via a scratch-arena clone and
/// leaves the caller's `&TermArena` unmutated — the property the bench/trait
/// (`&TermArena` only) needs. `x=1 ∧ x=2 ∧ r=p·q`: UNSAT with the multiplier
/// never materialized (`ops_refined == 0`).
#[test]
#[allow(clippy::many_single_char_names)] // x, p, q, r are natural BV-variable names
fn lazy_bv_ro_decides_without_mutating_caller_arena() {
    let mut a = TermArena::new();
    let xs = a.declare("x", Sort::BitVec(32)).unwrap();
    let ps = a.declare("p", Sort::BitVec(32)).unwrap();
    let qs = a.declare("q", Sort::BitVec(32)).unwrap();
    let rs = a.declare("r", Sort::BitVec(32)).unwrap();
    let x = a.var(xs);
    let p = a.var(ps);
    let q = a.var(qs);
    let r = a.var(rs);
    let one = a.bv_const(32, 1).unwrap();
    let two = a.bv_const(32, 2).unwrap();
    let mul = a.bv_mul(p, q).unwrap();
    let c1 = a.eq(x, one).unwrap();
    let c2 = a.eq(x, two).unwrap();
    let c3 = a.eq(r, mul).unwrap();
    let assertions = [c1, c2, c3];

    let len_before = a.len();
    // `&a` — immutable borrow, mirroring the `SolverBackend::check` contract.
    let outcome = check_lazy_bv_abstraction_ro(&a, &assertions, &SolverConfig::default()).unwrap();
    let len_after = a.len();

    assert!(
        matches!(outcome.result, CheckResult::Unsat),
        "RO lazy must decide UNSAT, got {:?}",
        outcome.result
    );
    assert_eq!(
        outcome.ops_refined, 0,
        "incidental multiplier must never be materialized"
    );
    assert_eq!(
        outcome.ops_total, 1,
        "exactly one heavy op (the bvmul) present"
    );
    assert_eq!(
        len_before, len_after,
        "caller's arena must be untouched (the strategy ran on a clone)"
    );
}

/// `LazyBvBackend` decides through the `SolverBackend` trait (the bench's
/// consumer interface) and reports refinement telemetry in `last_stats`.
#[test]
#[allow(clippy::many_single_char_names)] // x, p, q, r are natural BV-variable names
fn lazy_bv_backend_via_trait_reports_telemetry() {
    let mut a = TermArena::new();
    let xs = a.declare("x", Sort::BitVec(16)).unwrap();
    let ps = a.declare("p", Sort::BitVec(16)).unwrap();
    let qs = a.declare("q", Sort::BitVec(16)).unwrap();
    let rs = a.declare("r", Sort::BitVec(16)).unwrap();
    let x = a.var(xs);
    let p = a.var(ps);
    let q = a.var(qs);
    let r = a.var(rs);
    let one = a.bv_const(16, 1).unwrap();
    let two = a.bv_const(16, 2).unwrap();
    let mul = a.bv_mul(p, q).unwrap();
    let c1 = a.eq(x, one).unwrap();
    let c2 = a.eq(x, two).unwrap();
    let c3 = a.eq(r, mul).unwrap();

    let mut backend = LazyBvBackend::new();
    let result = backend
        .check(&a, &[c1, c2, c3], &SolverConfig::default())
        .unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "trait check must decide UNSAT, got {result:?}"
    );
    let stats = backend.last_stats().expect("lazy backend records stats");
    let counter = |name: &str| {
        stats
            .backend
            .iter()
            .find(|(k, _)| k == name)
            .map(|(_, v)| *v)
    };
    assert_eq!(counter("lazy_ops_total"), Some(1.0), "one heavy op present");
    assert_eq!(
        counter("lazy_ops_refined"),
        Some(0.0),
        "incidental multiplier never materialized"
    );
}

// --- ite abstraction (P2.1 lever #3: broaden beyond arithmetic) ---------------

/// With `lazy_bv_abstract_ite` ON, a BV-sorted `ite` incidental to a non-ite
/// contradiction (`x=1 ∧ x=2`) is abstracted and never materialized: UNSAT with
/// `ops_total == 1` (the ite) and `ops_refined == 0`.
#[test]
#[allow(clippy::many_single_char_names)] // x, c, p, q, y are natural names here
fn lazy_ite_incidental_unsat_abstracts_the_ite() {
    let mut a = TermArena::new();
    let xs = a.declare("x", Sort::BitVec(8)).unwrap();
    let cs = a.declare("c", Sort::Bool).unwrap();
    let ps = a.declare("p", Sort::BitVec(8)).unwrap();
    let qs = a.declare("q", Sort::BitVec(8)).unwrap();
    let ys = a.declare("y", Sort::BitVec(8)).unwrap();
    let x = a.var(xs);
    let c = a.var(cs);
    let p = a.var(ps);
    let q = a.var(qs);
    let y = a.var(ys);
    let ite = a.ite(c, p, q).unwrap();
    let one = a.bv_const(8, 1).unwrap();
    let two = a.bv_const(8, 2).unwrap();
    let e1 = a.eq(y, ite).unwrap();
    let e2 = a.eq(x, one).unwrap();
    let e3 = a.eq(x, two).unwrap();

    let cfg = SolverConfig::default().with_lazy_bv_abstract_ite(true);
    let outcome = check_lazy_bv_abstraction_ro(&a, &[e1, e2, e3], &cfg).unwrap();
    assert!(
        matches!(outcome.result, CheckResult::Unsat),
        "must decide UNSAT, got {:?}",
        outcome.result
    );
    assert_eq!(outcome.ops_total, 1, "the BV ite is the one heavy op");
    assert_eq!(outcome.ops_refined, 0, "incidental ite never materialized");
}

/// With the flag OFF, the same `ite`-only formula has no heavy ops to abstract
/// (`ops_total == 0`) — the default behavior is unchanged.
#[test]
#[allow(clippy::many_single_char_names)]
fn lazy_ite_flag_off_does_not_abstract_ite() {
    let mut a = TermArena::new();
    let cs = a.declare("c", Sort::Bool).unwrap();
    let ps = a.declare("p", Sort::BitVec(8)).unwrap();
    let qs = a.declare("q", Sort::BitVec(8)).unwrap();
    let ys = a.declare("y", Sort::BitVec(8)).unwrap();
    let c = a.var(cs);
    let p = a.var(ps);
    let q = a.var(qs);
    let y = a.var(ys);
    let ite = a.ite(c, p, q).unwrap();
    let e1 = a.eq(y, ite).unwrap();
    let five = a.bv_const(8, 5).unwrap();
    let e2 = a.eq(p, five).unwrap();

    let cfg = SolverConfig::default(); // abstract_ite off
    let outcome = check_lazy_bv_abstraction_ro(&a, &[e1, e2], &cfg).unwrap();
    assert_eq!(
        outcome.ops_total, 0,
        "ite must not be abstracted when the flag is off"
    );
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "trivially sat, got {:?}",
        outcome.result
    );
}

/// An `ite` whose value is essential to the verdict forces a refinement:
/// `y = ite(c,1,2) ∧ y = 99` is UNSAT, reachable only after the abstract `ite`
/// is refined to its exact definition. `ops_refined == 1`.
#[test]
#[allow(clippy::many_single_char_names)]
fn lazy_ite_essential_unsat_via_refinement() {
    let mut a = TermArena::new();
    let cs = a.declare("c", Sort::Bool).unwrap();
    let ys = a.declare("y", Sort::BitVec(8)).unwrap();
    let c = a.var(cs);
    let y = a.var(ys);
    let one = a.bv_const(8, 1).unwrap();
    let two = a.bv_const(8, 2).unwrap();
    let ninety_nine = a.bv_const(8, 99).unwrap();
    let ite = a.ite(c, one, two).unwrap();
    let e1 = a.eq(y, ite).unwrap();
    let e2 = a.eq(y, ninety_nine).unwrap();

    let cfg = SolverConfig::default().with_lazy_bv_abstract_ite(true);
    let outcome = check_lazy_bv_abstraction_ro(&a, &[e1, e2], &cfg).unwrap();
    assert!(
        matches!(outcome.result, CheckResult::Unsat),
        "y=ite(c,1,2) ∧ y=99 is UNSAT, got {:?}",
        outcome.result
    );
    assert_eq!(outcome.ops_total, 1, "one BV ite");
    assert_eq!(
        outcome.ops_refined, 1,
        "the ite is essential and must be refined"
    );
}

/// On a sat instance whose model exercises the `ite`, ite-abstraction agrees with
/// eager (both sat) and yields a replayed model.
#[test]
#[allow(clippy::many_single_char_names)]
fn lazy_ite_sat_agrees_with_eager() {
    fn build(a: &mut TermArena) -> Vec<axeyum_ir::TermId> {
        let cs = a.declare("c", Sort::Bool).unwrap();
        let p = a.declare("p", Sort::BitVec(8)).unwrap();
        let q = a.declare("q", Sort::BitVec(8)).unwrap();
        let ys = a.declare("y", Sort::BitVec(8)).unwrap();
        let c = a.var(cs);
        let pv = a.var(p);
        let qv = a.var(q);
        let y = a.var(ys);
        let ite = a.ite(c, pv, qv).unwrap();
        let seven = a.bv_const(8, 7).unwrap();
        let e1 = a.eq(y, ite).unwrap();
        let e2 = a.eq(pv, seven).unwrap();
        let e3 = a.eq(y, seven).unwrap();
        vec![c, e1, e2, e3] // c forces the then-branch; y=p=7 is sat
    }
    let mut a1 = TermArena::new();
    let asserts1 = build(&mut a1);
    let eager = solve(&mut a1, &asserts1, &SolverConfig::default()).unwrap();
    let mut a2 = TermArena::new();
    let asserts2 = build(&mut a2);
    let lazy = check_lazy_bv_abstraction_ro(
        &a2,
        &asserts2,
        &SolverConfig::default().with_lazy_bv_abstract_ite(true),
    )
    .unwrap();
    assert!(matches!(eager, CheckResult::Sat(_)), "eager sat: {eager:?}");
    assert!(
        matches!(lazy.result, CheckResult::Sat(_)),
        "ite-lazy must be sat, got {:?}",
        lazy.result
    );
}
