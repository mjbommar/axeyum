//! Tiny-witness `QF_NIA` satisfiability via the no-overflow multiplier
//! side-constraint on the integer bit-blast.
//!
//! Before the constraint, a nonlinear product `x*y` bit-blasted at width `B`
//! could be satisfied by a *wrapping* (mod 2^B) model that the exact-integer
//! replay correctly rejects, so these queries returned `Unknown` even though a
//! tiny genuine witness exists. The no-overflow constraint forces the SAT search
//! onto the faithful (non-wrapping) product, so the small witness is found and
//! replays exactly. Soundness is unchanged: every `Sat` below is independently
//! re-checked against the *original* integer assertions, and a bounded
//! non-refutation must stay `Unknown` (never `Unsat`).
#![cfg(feature = "full")]

use axeyum_ir::{TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, solve};

/// Re-check a `Sat` independently: every original assertion must evaluate to
/// `true` over exact integer semantics under the projected model.
fn assert_sat_replays(result: &CheckResult, arena: &TermArena, assertions: &[TermId]) {
    let CheckResult::Sat(model) = result else {
        panic!("expected Sat, got {result:?}");
    };
    let assignment = model.to_assignment();
    for &a in assertions {
        assert!(
            matches!(eval(arena, a, &assignment), Ok(Value::Bool(true))),
            "Sat model must satisfy original assertion on exact-integer replay (assertion {a:?})"
        );
    }
}

#[test]
fn tiny_witness_3xy_plus3_gt0_and_neg_x_minus2_eq0() {
    // 3*x*y + 3 > 0  ∧  -x - 2 = 0   ⇒  x = -2, y = 0  (3*(-2)*0 + 3 = 3 > 0).
    // The witness product x*y = 0 is non-wrapping; the constraint guides the
    // search straight to it. Was `Unknown` (the blast found a wrapping model).
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let three = arena.int_const(3);
    let xy = arena.int_mul(x, y).unwrap();
    let three_xy = arena.int_mul(three, xy).unwrap();
    let lhs1 = arena.int_add(three_xy, three).unwrap();
    let zero = arena.int_const(0);
    let a1 = arena.int_gt(lhs1, zero).unwrap();
    // -x - 2 = 0
    let neg_x = arena.int_neg(x).unwrap();
    let two = arena.int_const(2);
    let lhs2 = arena.int_sub(neg_x, two).unwrap();
    let zero2 = arena.int_const(0);
    let a2 = arena.eq(lhs2, zero2).unwrap();

    let assertions = [a1, a2];
    let result = solve(&mut arena, &assertions, &SolverConfig::default()).unwrap();
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "expected Sat (x=-2,y=0), got {result:?}"
    );
    assert_sat_replays(&result, &arena, &assertions);
}

#[test]
fn tiny_witness_neg3xy_minus3_eq0_and_2x_lt0() {
    // -3*x*y - 3 = 0  ∧  2*x < 0   ⇒  x = -1, y = 1  (-3*(-1)*1 - 3 = 0).
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let neg3 = arena.int_const(-3);
    let xy = arena.int_mul(x, y).unwrap();
    let neg3_xy = arena.int_mul(neg3, xy).unwrap();
    let three = arena.int_const(3);
    let lhs1 = arena.int_sub(neg3_xy, three).unwrap();
    let zero = arena.int_const(0);
    let a1 = arena.eq(lhs1, zero).unwrap();
    // 2*x < 0
    let two = arena.int_const(2);
    let twox = arena.int_mul(two, x).unwrap();
    let zero2 = arena.int_const(0);
    let a2 = arena.int_lt(twox, zero2).unwrap();

    let assertions = [a1, a2];
    let result = solve(&mut arena, &assertions, &SolverConfig::default()).unwrap();
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "expected Sat (x=-1,y=1), got {result:?}"
    );
    assert_sat_replays(&result, &arena, &assertions);
}

#[test]
fn genuine_nonlinear_unsat_stays_unknown_not_unsat() {
    // x*y = 1 ∧ x + y = 3  over the integers: the only factorizations of 1 are
    // (1,1) and (-1,-1), giving sums 2 and -2, never 3 ⇒ truly UNSAT. The
    // bounded bit-blast cannot *refute* this (no exhaustive integer reasoning),
    // and the no-overflow constraint must NOT turn that bounded non-refutation
    // into a wrong `Unsat`. A sound result is `Unknown` (or, if some engine can
    // refute it exactly, `Unsat`) — but NEVER `Sat`.
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let xy = arena.int_mul(x, y).unwrap();
    let one = arena.int_const(1);
    let a1 = arena.eq(xy, one).unwrap();
    let sum = arena.int_add(x, y).unwrap();
    let three = arena.int_const(3);
    let a2 = arena.eq(sum, three).unwrap();

    let assertions = [a1, a2];
    let result = solve(&mut arena, &assertions, &SolverConfig::default()).unwrap();
    assert!(
        !matches!(result, CheckResult::Sat(_)),
        "x*y=1 ∧ x+y=3 has no integer solution; must never be Sat, got {result:?}"
    );
}

#[test]
fn large_product_witness_decides_or_stays_unknown_never_wrong() {
    // x*y = 1000000 ∧ x - y = 0  ⇒  x = y = 1000 (product 10^6 needs ≥ ~21 bits).
    // The width ladder must widen to a width where the faithful product fits, and
    // either decide `Sat` (replay-checked) or stay a sound `Unknown` — never a
    // wrong verdict.
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let xy = arena.int_mul(x, y).unwrap();
    let big = arena.int_const(1_000_000);
    let a1 = arena.eq(xy, big).unwrap();
    let diff = arena.int_sub(x, y).unwrap();
    let zero = arena.int_const(0);
    let a2 = arena.eq(diff, zero).unwrap();

    let assertions = [a1, a2];
    let result = solve(&mut arena, &assertions, &SolverConfig::default()).unwrap();
    match result {
        CheckResult::Sat(_) => assert_sat_replays(&result, &arena, &assertions),
        CheckResult::Unknown(_) => {} // sound: bounded incompleteness
        CheckResult::Unsat => panic!("x*y=10^6 ∧ x=y is satisfiable (x=y=1000); wrong Unsat"),
    }
}
