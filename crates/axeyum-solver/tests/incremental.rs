//! Tests for the incremental [`Solver`] façade.
//!
//! These exercise the symbolic-execution-shaped surface: assertion stacking,
//! `push`/`pop` scopes, and one-shot `check_assuming` assumptions, all over the
//! pure-Rust backend. The scenario catalog is also driven through the façade to
//! confirm it is a drop-in front end for the conformance corpus.
#![cfg(feature = "full")]

use axeyum_ir::{Sort, TermArena, Value, eval};
use axeyum_scenarios::{Expectation, catalog};
use axeyum_solver::{CheckResult, SatBvBackend, Solver};

#[test]
fn push_pop_scopes_restore_assertions() {
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(8)).unwrap();
    let x = arena.var(x_sym);
    let ten = arena.bv_const(8, 10).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let x_lt_10 = arena.bv_ult(x, ten).unwrap();
    let x_ge_10 = arena.bv_uge(x, ten).unwrap();
    let x_is_zero = arena.eq(x, zero).unwrap();

    let mut solver = Solver::new(SatBvBackend::new());
    solver.assert(x_lt_10);
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Sat(_)));

    // A contradictory scope is unsat; popping it restores satisfiability.
    solver.push();
    solver.assert(x_ge_10);
    assert_eq!(solver.scope_depth(), 1);
    assert_eq!(solver.check(&arena).unwrap(), CheckResult::Unsat);
    assert!(solver.pop());
    assert_eq!(solver.scope_depth(), 0);
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Sat(_)));

    // Popping with no open scope is a graceful no-op.
    assert!(!solver.pop());

    // The remaining assertion still constrains the model.
    solver.push();
    solver.assert(x_is_zero);
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

    let mut solver = Solver::new(SatBvBackend::new());
    solver.assert(x_is_three);

    // The assumption contradicts the assertion: unsat for this check only.
    assert_eq!(
        solver.check_assuming(&arena, &[x_is_seven]).unwrap(),
        CheckResult::Unsat
    );
    // Without the assumption, the base assertion is satisfiable again.
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Sat(_)));
    assert_eq!(solver.assertions(), &[x_is_three]);
}

#[test]
fn facade_decides_scenario_catalog() {
    let mut decided = 0usize;
    for scenario in catalog() {
        let mut solver = Solver::new(SatBvBackend::new());
        solver.assert_all(&scenario.query.solver_terms().collect::<Vec<_>>());
        let result = solver
            .check(&scenario.arena)
            .unwrap_or_else(|error| panic!("scenario {} errored: {error}", scenario.name));
        match (&scenario.expectation, &result) {
            (Expectation::Sat { .. }, CheckResult::Sat(model)) => {
                let assignment = model.to_assignment();
                for term in scenario.query.solver_terms() {
                    assert_eq!(
                        eval(&scenario.arena, term, &assignment).unwrap(),
                        Value::Bool(true),
                        "facade model must satisfy {}",
                        scenario.name
                    );
                }
                decided += 1;
            }
            (Expectation::Unsat { .. }, CheckResult::Unsat) => decided += 1,
            (expectation, actual) => panic!(
                "facade disagreed on {}: expected {expectation:?}, got {actual:?}",
                scenario.name
            ),
        }
    }
    assert!(decided > 0, "catalog must not be empty");
}
