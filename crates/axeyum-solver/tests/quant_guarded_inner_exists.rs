//! Guarded-finite-`Int` universal whose body carries an **inner existential**:
//! `∀x:Int. (lo≤x≤hi) ⇒ ∃y. P(x, y)`. After the guarded expansion this is
//! `⋀_{v=lo}^{hi} ∃y. P(v, y)`; skolemizing each (positive) `∃y` to a fresh
//! witness lets the ordinary quantifier-free dispatch decide it. The expansion
//! is equivalence-preserving and the positive skolemization is equisatisfiable,
//! so both the `sat` and `unsat` verdicts transfer — and every `sat` is replayed
//! against the (rewritten, equisatisfiable) assertions.
//!
//! Soundness focus: a body whose inner `∃y` is *unsatisfiable for each `x`* makes
//! the whole guarded universal false; the engine must then decide `Unsat`
//! (or a sound `Unknown`) — never a wrong `Sat`.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(60))
}

fn decide(arena: &mut TermArena, assertions: &[TermId]) -> CheckResult {
    solve(arena, assertions, &config()).expect("solve decides or returns unknown without error")
}

/// Builds `∀x:Int. (lo <= x ∧ x <= hi) ⇒ ∃y:Int. inner(x, y)`, where `inner` is
/// produced from the outer bound-variable term `x` and the inner bound-variable
/// term `y` by `build_inner`.
fn guarded_forall_inner_exists(
    arena: &mut TermArena,
    lo: i128,
    hi: i128,
    build_inner: impl FnOnce(&mut TermArena, TermId, TermId) -> TermId,
) -> TermId {
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let y_sym = arena.declare("y", Sort::Int).unwrap();
    let y = arena.var(y_sym);

    let lo_c = arena.int_const(lo);
    let hi_c = arena.int_const(hi);
    let lower = arena.int_le(lo_c, x).unwrap(); // lo <= x
    let upper = arena.int_le(x, hi_c).unwrap(); // x <= hi
    let guard = arena.and(lower, upper).unwrap();

    let inner = build_inner(arena, x, y);
    let exists = arena.exists(y_sym, inner).unwrap();
    let body = arena.implies(guard, exists).unwrap();
    arena.forall(x_sym, body).unwrap()
}

// --- DECIDES: must be Sat, model replays ----------------------------------

#[test]
fn forall_guarded_inner_exists_square_is_sat() {
    // ∀x:Int. (0<=x<=3) ⇒ ∃y. y = x*x  — each conjunct ∃y.y=v*v is witnessed by
    // y=v*v, so the whole is Sat. (The headline gap.)
    let mut arena = TermArena::new();
    let all = guarded_forall_inner_exists(&mut arena, 0, 3, |arena, x, y| {
        let sq = arena.int_mul(x, x).unwrap();
        arena.eq(y, sq).unwrap()
    });
    let result = decide(&mut arena, &[all]);
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "∀x.(0<=x<=3)⇒∃y.y=x*x must decide Sat, got {result:?}"
    );
}

#[test]
fn forall_guarded_inner_exists_greater_is_sat() {
    // ∀x:Int. (0<=x<=2) ⇒ ∃y. y > x  — each ∃y.y>v witnessed by y=v+1, so Sat.
    let mut arena = TermArena::new();
    let all =
        guarded_forall_inner_exists(&mut arena, 0, 2, |arena, x, y| arena.int_gt(y, x).unwrap());
    let result = decide(&mut arena, &[all]);
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "∀x.(0<=x<=2)⇒∃y.y>x must decide Sat, got {result:?}"
    );
}

#[test]
fn one_point_inner_exists_is_sat() {
    // ∀x:Int. (2<=x<=2) ⇒ ∃y. y = x + 1  — single point, ∃y.y=3 holds. Sat.
    let mut arena = TermArena::new();
    let all = guarded_forall_inner_exists(&mut arena, 2, 2, |arena, x, y| {
        let one = arena.int_const(1);
        let succ = arena.int_add(x, one).unwrap();
        arena.eq(y, succ).unwrap()
    });
    let result = decide(&mut arena, &[all]);
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "one-point guarded ∀ with inner ∃ must decide Sat, got {result:?}"
    );
}

// --- SOUNDNESS NEGATIVES: never a wrong Sat -------------------------------

#[test]
fn inner_exists_unsatisfiable_is_unsat_never_wrong_sat() {
    // ∀x:Int. (0<=x<=2) ⇒ ∃y. (y > x ∧ y < x). The inner ∃y is unsatisfiable for
    // every x (no y with v < y < v), so each conjunct is false ⇒ the guarded
    // universal is FALSE ⇒ the assertion is Unsat. It must NOT be a wrong Sat;
    // a sound Unknown is also acceptable but here it decides Unsat.
    let mut arena = TermArena::new();
    let all = guarded_forall_inner_exists(&mut arena, 0, 2, |arena, x, y| {
        let gt = arena.int_gt(y, x).unwrap();
        let lt = arena.int_lt(y, x).unwrap();
        arena.and(gt, lt).unwrap()
    });
    let result = decide(&mut arena, &[all]);
    assert!(
        matches!(result, CheckResult::Unsat | CheckResult::Unknown(_)),
        "inner-∃-unsat guarded ∀ must be Unsat or sound Unknown, never Sat, got {result:?}"
    );
}

#[test]
fn mixed_inner_exists_partially_unsat_is_unsat_never_wrong_sat() {
    // ∀x:Int. (0<=x<=3) ⇒ ∃y. (y = x*x ∧ y < 4). For x∈{0,1} a witness exists
    // (0<4, 1<4); for x∈{2,3} no y (4,9 are not < 4), so the conjunct fails ⇒
    // the universal is FALSE ⇒ Unsat. Must not be a wrong Sat.
    let mut arena = TermArena::new();
    let all = guarded_forall_inner_exists(&mut arena, 0, 3, |arena, x, y| {
        let sq = arena.int_mul(x, x).unwrap();
        let eq = arena.eq(y, sq).unwrap();
        let four = arena.int_const(4);
        let lt = arena.int_lt(y, four).unwrap();
        arena.and(eq, lt).unwrap()
    });
    let result = decide(&mut arena, &[all]);
    assert!(
        matches!(result, CheckResult::Unsat | CheckResult::Unknown(_)),
        "partially-unsat inner-∃ guarded ∀ must be Unsat or sound Unknown, got {result:?}"
    );
}
