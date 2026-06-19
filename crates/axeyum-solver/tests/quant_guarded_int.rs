//! Guarded-finite-`Int` universal expansion: a universal `∀x:Int. (lo<=x<=hi)
//! => inner` is *logically equivalent* to the finite conjunction
//! `⋀_{v=lo}^{hi} inner[x:=v]` (outside `[lo, hi]` the implication is vacuously
//! true), so the solver decides it exactly through ordinary dispatch — both the
//! valid (`sat`) and the refuted (`unsat`) directions. A range over the
//! deterministic size cap is left as a sound `unknown` (never a wrong answer,
//! never an OOM).

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(60))
}

fn decide(arena: &mut TermArena, assertions: &[TermId]) -> CheckResult {
    // `solve` must never error on these shapes — it either decides or returns a
    // sound `Unknown`.
    solve(arena, assertions, &config()).expect("solve decides or returns unknown without error")
}

/// Builds `∀x:Int. (lo <= x ∧ x <= hi) => inner`, where `inner` is produced from
/// the bound-variable term by `build_inner`.
fn guarded_forall(
    arena: &mut TermArena,
    lo: i128,
    hi: i128,
    build_inner: impl FnOnce(&mut TermArena, TermId) -> TermId,
) -> TermId {
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let lo_c = arena.int_const(lo);
    let hi_c = arena.int_const(hi);
    let lower = arena.int_le(lo_c, x).unwrap(); // lo <= x
    let upper = arena.int_le(x, hi_c).unwrap(); // x <= hi
    let guard = arena.and(lower, upper).unwrap();
    let inner = build_inner(arena, x);
    let body = arena.implies(guard, inner).unwrap();
    arena.forall(x_sym, body).unwrap()
}

#[test]
fn valid_universal_over_finite_int_range_is_sat() {
    // ∀x:Int. (1<=x ∧ x<=3) => x*x <= 9  — true for x∈{1,2,3}, so valid (sat).
    let mut arena = TermArena::new();
    let all = guarded_forall(&mut arena, 1, 3, |arena, x| {
        let sq = arena.int_mul(x, x).unwrap();
        let nine = arena.int_const(9);
        arena.int_le(sq, nine).unwrap()
    });
    assert!(
        matches!(decide(&mut arena, &[all]), CheckResult::Sat(_)),
        "valid guarded-Int universal must decide sat"
    );
}

#[test]
fn refuted_universal_over_finite_int_range_is_unsat() {
    // ∀x:Int. (1<=x ∧ x<=3) => x <= 2  — fails at x=3, so the universal is false
    // (its negation is satisfiable, the universal itself is unsat as an assertion).
    let mut arena = TermArena::new();
    let all = guarded_forall(&mut arena, 1, 3, |arena, x| {
        let two = arena.int_const(2);
        arena.int_le(x, two).unwrap()
    });
    assert!(
        matches!(decide(&mut arena, &[all]), CheckResult::Unsat),
        "refuted guarded-Int universal must decide unsat"
    );
}

#[test]
fn ge_oriented_guard_decides() {
    // ∀x:Int. (x>=1 ∧ x<=3) => x*x <= 9 — same fact, guard written with `>=`.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let one = arena.int_const(1);
    let three = arena.int_const(3);
    let lower = arena.int_ge(x, one).unwrap(); // x >= 1
    let upper = arena.int_le(x, three).unwrap(); // x <= 3
    let guard = arena.and(lower, upper).unwrap();
    let sq = arena.int_mul(x, x).unwrap();
    let nine = arena.int_const(9);
    let inner = arena.int_le(sq, nine).unwrap();
    let body = arena.implies(guard, inner).unwrap();
    let all = arena.forall(x_sym, body).unwrap();
    assert!(
        matches!(decide(&mut arena, &[all]), CheckResult::Sat(_)),
        ">=-oriented guard must decide sat"
    );
}

#[test]
fn one_point_range_decides() {
    // ∀x:Int. (2<=x ∧ x<=2) => x*x == 4 — a single point x=2; 2*2==4 holds (sat).
    let mut arena = TermArena::new();
    let all = guarded_forall(&mut arena, 2, 2, |arena, x| {
        let sq = arena.int_mul(x, x).unwrap();
        let four = arena.int_const(4);
        arena.eq(sq, four).unwrap()
    });
    assert!(
        matches!(decide(&mut arena, &[all]), CheckResult::Sat(_)),
        "one-point guarded range must decide sat"
    );

    // And the refuted one-point case: ∀x. (2<=x<=2) => x==3 is false.
    let mut arena = TermArena::new();
    let all_bad = guarded_forall(&mut arena, 2, 2, |arena, x| {
        let three = arena.int_const(3);
        arena.eq(x, three).unwrap()
    });
    assert!(
        matches!(decide(&mut arena, &[all_bad]), CheckResult::Unsat),
        "refuted one-point guarded range must decide unsat"
    );
}

#[test]
fn too_large_range_is_unknown_not_wrong() {
    // ∀x:Int. (0 <= x ∧ x <= 1_000_000) => x+1 >= x. The body is valid (so it
    // cannot be refuted by instantiation either), and the range is far over the
    // expansion cap, so the guarded pass declines to expand and the solver returns
    // a sound `Unknown` — never a wrong sat/unsat, never an OOM. This isolates the
    // cap: a smaller range over the same body decides `sat` (checked below).
    let mut arena = TermArena::new();
    let build = |arena: &mut TermArena, x: TermId| {
        let one = arena.int_const(1);
        let succ = arena.int_add(x, one).unwrap();
        arena.int_ge(succ, x).unwrap()
    };
    let all = guarded_forall(&mut arena, 0, 1_000_000, build);
    let result = decide(&mut arena, &[all]);
    assert!(
        matches!(result, CheckResult::Unknown(_)),
        "over-cap range must be Unknown (never a wrong answer / OOM), got {result:?}"
    );

    // The SAME body over a small in-cap range *does* decide sat: confirms it is
    // the range size, not the body, that gates expansion.
    let mut arena = TermArena::new();
    let small = guarded_forall(&mut arena, 0, 3, build);
    assert!(
        matches!(decide(&mut arena, &[small]), CheckResult::Sat(_)),
        "same body over a small range must decide sat"
    );
}
