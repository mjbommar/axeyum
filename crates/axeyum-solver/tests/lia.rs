//! End-to-end bounded `QF_LIA`: integer bit-blasting + pure-Rust BV solving
//! (ADR-0014).
//!
//! These tests exercise [`check_with_int_blasting`]: an integer query is
//! bit-blasted to signed `QF_BV`, solved by [`SatBvBackend`], and its model is
//! read back as exact integers and **replayed against the original integer
//! query** with the ground evaluator. The soundness contract is checked too:
//! `sat` is only returned when the exact-integer replay succeeds, and bounded
//! `unsat` is reported as `unknown`, never `unsat`.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, Value, eval};
use axeyum_solver::{
    CheckResult, DEFAULT_INT_WIDTH, SatBvBackend, SolverConfig, check_with_int_blasting,
};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

fn solve(arena: &mut TermArena, assertions: &[axeyum_ir::TermId], width: u32) -> CheckResult {
    let mut backend = SatBvBackend::new();
    check_with_int_blasting(&mut backend, arena, assertions, width, &config())
        .expect("supported `QF_LIA` query decides without error")
}

#[test]
fn linear_equation_is_satisfiable_and_replays_as_integers() {
    // x + 2 == 5 && x > 0 : satisfiable with x = 3.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let two = arena.int_const(2);
    let five = arena.int_const(5);
    let zero = arena.int_const(0);
    let sum = arena.int_add(x, two).unwrap();
    let eq = arena.eq(sum, five).unwrap();
    let pos = arena.int_gt(x, zero).unwrap();

    let CheckResult::Sat(model) = solve(&mut arena, &[eq, pos], DEFAULT_INT_WIDTH) else {
        panic!("expected satisfiable linear equation");
    };
    // The returned model is over the original integer symbol and replays true.
    assert_eq!(model.get(x_sym), Some(Value::Int(3)));
    let assignment = model.to_assignment();
    assert_eq!(eval(&arena, eq, &assignment).unwrap(), Value::Bool(true));
    assert_eq!(eval(&arena, pos, &assignment).unwrap(), Value::Bool(true));
}

#[test]
fn negative_solution_round_trips() {
    // x + 5 == 2 : satisfiable with x = -3 (exercises signed encoding).
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let five = arena.int_const(5);
    let two = arena.int_const(2);
    let sum = arena.int_add(x, five).unwrap();
    let eq = arena.eq(sum, two).unwrap();

    let CheckResult::Sat(model) = solve(&mut arena, &[eq], 16) else {
        panic!("expected satisfiable equation with negative solution");
    };
    assert_eq!(model.get(x_sym), Some(Value::Int(-3)));
}

#[test]
fn contradictory_bounds_are_unknown_not_unsat() {
    // x > 0 && x < 0 : has no model in range. Bounded blasting must report
    // `unknown` (the contract forbids claiming `unsat`).
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.int_const(0);
    let gt = arena.int_gt(x, zero).unwrap();
    let lt = arena.int_lt(x, zero).unwrap();

    let result = solve(&mut arena, &[gt, lt], 16);
    assert!(
        matches!(result, CheckResult::Unknown(_)),
        "bounded unsat must be reported as unknown, got {result:?}"
    );
}

#[test]
fn relational_constraint_between_two_integers() {
    // x < y && y < x + 1 : forces y == x + ... no integer between, so within a
    // single unit it pins y = x + nothing? x < y < x+1 has no integer solution;
    // must be unknown (bounded). Use a satisfiable variant instead:
    // x < y && x + 10 == y : satisfiable (y = x + 10, e.g. x=0, y=10).
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let y_sym = arena.declare("y", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let ten = arena.int_const(10);
    let less = arena.int_lt(x, y).unwrap();
    let shifted = arena.int_add(x, ten).unwrap();
    let eq = arena.eq(shifted, y).unwrap();

    let CheckResult::Sat(model) = solve(&mut arena, &[less, eq], DEFAULT_INT_WIDTH) else {
        panic!("expected satisfiable relational constraint");
    };
    let assignment = model.to_assignment();
    assert_eq!(eval(&arena, less, &assignment).unwrap(), Value::Bool(true));
    assert_eq!(eval(&arena, eq, &assignment).unwrap(), Value::Bool(true));
}

#[test]
fn out_of_range_constant_is_unknown() {
    // A constant that overflows the chosen narrow bound yields `unknown`, not an
    // error and not a wrong answer.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let big = arena.int_const(100_000); // doesn't fit signed 8 bits
    let eq = arena.eq(x, big).unwrap();

    let result = solve(&mut arena, &[eq], 8);
    assert!(
        matches!(result, CheckResult::Unknown(_)),
        "out-of-range constant must be unknown, got {result:?}"
    );
}
