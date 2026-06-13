//! Tests for the end-to-end incremental BV solver (ADR-0009 stage 2).
//!
//! The warm incremental engine must agree with the oracle-free scenario ground
//! truth, and its push/pop scopes and one-shot assumptions must behave like
//! SMT-LIB incremental solving — all with model replay against the original
//! terms.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, Value, eval};
use axeyum_scenarios::{Expectation, catalog};
use axeyum_solver::{CheckResult, IncrementalBvSolver, SolverConfig};

const TIMEOUT: Duration = Duration::from_secs(30);

#[test]
fn incremental_solver_decides_scenario_catalog() {
    for scenario in catalog() {
        let mut solver =
            IncrementalBvSolver::with_config(SolverConfig::new().with_timeout(TIMEOUT));
        for term in scenario.query.solver_terms() {
            solver
                .assert(&scenario.arena, term)
                .unwrap_or_else(|error| {
                    panic!("scenario {} assert errored: {error}", scenario.name)
                });
        }
        let result = solver
            .check(&scenario.arena)
            .unwrap_or_else(|error| panic!("scenario {} check errored: {error}", scenario.name));

        match (&scenario.expectation, &result) {
            (Expectation::Sat { .. }, CheckResult::Sat(model)) => {
                let assignment = model.to_assignment();
                for term in scenario.query.solver_terms() {
                    assert_eq!(
                        eval(&scenario.arena, term, &assignment).unwrap(),
                        Value::Bool(true),
                        "incremental model must satisfy {}",
                        scenario.name
                    );
                }
            }
            (Expectation::Unsat { .. }, CheckResult::Unsat) => {}
            (Expectation::Sat { .. }, CheckResult::Unsat) => {
                panic!(
                    "SOUNDNESS: incremental reported unsat for satisfiable {}",
                    scenario.name
                )
            }
            (Expectation::Unsat { .. }, CheckResult::Sat(_)) => {
                panic!(
                    "SOUNDNESS: incremental reported sat for unsatisfiable {}",
                    scenario.name
                )
            }
            (_, CheckResult::Unknown(reason)) => {
                panic!("scenario {} returned unknown: {reason:?}", scenario.name)
            }
        }
    }
}

#[test]
fn push_pop_scopes_enable_and_disable_assertions() {
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(8)).unwrap();
    let x = arena.var(x_sym);
    let ten = arena.bv_const(8, 10).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let x_lt_10 = arena.bv_ult(x, ten).unwrap();
    let x_ge_10 = arena.bv_uge(x, ten).unwrap();
    let x_is_zero = arena.eq(x, zero).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver.assert(&arena, x_lt_10).unwrap();
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Sat(_)));

    // A contradictory scope is unsat; popping it restores satisfiability,
    // without re-bit-blasting the base constraint.
    solver.push().unwrap();
    solver.assert(&arena, x_ge_10).unwrap();
    assert_eq!(solver.scope_depth(), 1);
    assert_eq!(solver.check(&arena).unwrap(), CheckResult::Unsat);
    assert!(solver.pop());
    assert_eq!(solver.scope_depth(), 0);
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Sat(_)));
    assert!(!solver.pop(), "cannot pop the base frame");

    // The surviving base assertion still constrains the model.
    solver.push().unwrap();
    solver.assert(&arena, x_is_zero).unwrap();
    let CheckResult::Sat(model) = solver.check(&arena).unwrap() else {
        panic!("expected sat");
    };
    assert_eq!(model.get(x_sym), Some(Value::Bv { width: 8, value: 0 }));
}

#[test]
fn check_assuming_does_not_persist() {
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(8)).unwrap();
    let x = arena.var(x_sym);
    let three = arena.bv_const(8, 3).unwrap();
    let seven = arena.bv_const(8, 7).unwrap();
    let x_is_three = arena.eq(x, three).unwrap();
    let x_is_seven = arena.eq(x, seven).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver.assert(&arena, x_is_three).unwrap();

    // The assumption contradicts the assertion: unsat for this check only.
    assert_eq!(
        solver.check_assuming(&arena, &[x_is_seven]).unwrap(),
        CheckResult::Unsat
    );
    // Without the assumption, the base assertion is satisfiable again, and the
    // ephemeral assumption clause did not persist.
    let CheckResult::Sat(model) = solver.check(&arena).unwrap() else {
        panic!("expected sat after dropping the assumption");
    };
    assert_eq!(model.get(x_sym), Some(Value::Bv { width: 8, value: 3 }));
}

#[test]
fn symbolic_execution_style_path_exploration() {
    // Mimic exploring two branches of `if (x + 1 == y) ... else ...` down one
    // warm solver: shared prefix asserted once, branches pushed/popped.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y_sym = arena.declare("y", Sort::BitVec(8)).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let one = arena.bv_const(8, 1).unwrap();
    let x_plus_1 = arena.bv_add(x, one).unwrap();
    let branch = arena.eq(x_plus_1, y).unwrap();

    let hundred = arena.bv_const(8, 100).unwrap();
    let x_lt_100 = arena.bv_ult(x, hundred).unwrap();
    let not_branch = arena.not(branch).unwrap();

    let mut solver = IncrementalBvSolver::new();
    // Shared path prefix: x < 100, bit-blasted once.
    solver.assert(&arena, x_lt_100).unwrap();

    // Then-branch: x + 1 == y is satisfiable.
    solver.push().unwrap();
    solver.assert(&arena, branch).unwrap();
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Sat(_)));
    solver.pop();

    // Else-branch: x + 1 != y is also satisfiable (the prefix was not re-blasted).
    solver.push().unwrap();
    solver.assert(&arena, not_branch).unwrap();
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Sat(_)));
    solver.pop();
}
