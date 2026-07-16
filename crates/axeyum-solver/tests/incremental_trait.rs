//! Conformance tests for the first-class retained incremental trait (ADR-0201).

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, IncrementalBvSolver, IncrementalSolver, SolverError};

fn exercise_retained_lifecycle(
    solver: &mut dyn IncrementalSolver,
    arena: &TermArena,
    base: TermId,
    contradiction: TermId,
) {
    solver.assert(arena, base).unwrap();
    assert!(matches!(solver.check(arena).unwrap(), CheckResult::Sat(_)));

    solver.push().unwrap();
    assert_eq!(solver.scope_depth(), 1);
    solver.assert(arena, contradiction).unwrap();
    assert_eq!(solver.check(arena).unwrap(), CheckResult::Unsat);
    assert!(solver.pop());
    assert_eq!(solver.scope_depth(), 0);
    assert!(!solver.pop(), "the base frame must not be popped");

    assert_eq!(
        solver.check_assuming(arena, &[contradiction]).unwrap(),
        CheckResult::Unsat
    );
    assert!(
        matches!(solver.check(arena).unwrap(), CheckResult::Sat(_)),
        "a one-shot assumption must not persist"
    );
}

#[test]
fn concrete_solver_satisfies_generic_retained_contract() {
    fn run<S: IncrementalSolver>(
        solver: &mut S,
        arena: &TermArena,
        base: TermId,
        contradiction: TermId,
    ) {
        exercise_retained_lifecycle(solver, arena, base, contradiction);
    }

    let (arena, base, contradiction) = fixture();
    let mut solver = IncrementalBvSolver::new();
    run(&mut solver, &arena, base, contradiction);
}

#[test]
fn retained_contract_is_object_safe() {
    let (arena, base, contradiction) = fixture();
    let mut solver: Box<dyn IncrementalSolver> = Box::new(IncrementalBvSolver::new());
    exercise_retained_lifecycle(solver.as_mut(), &arena, base, contradiction);
}

#[test]
fn trait_preserves_non_boolean_errors() {
    let mut arena = TermArena::new();
    let value = arena.bv_const(8, 1).unwrap();
    let mut solver = IncrementalBvSolver::new();
    let session: &mut dyn IncrementalSolver = &mut solver;

    assert_eq!(
        session.assert(&arena, value),
        Err(SolverError::NonBooleanAssertion(value))
    );
    assert_eq!(
        session.check_assuming(&arena, &[value]),
        Err(SolverError::NonBooleanAssertion(value))
    );
    assert_eq!(session.scope_depth(), 0);
}

fn fixture() -> (TermArena, TermId, TermId) {
    let mut arena = TermArena::new();
    let symbol = arena
        .declare("incremental_trait_x", Sort::BitVec(8))
        .unwrap();
    let variable = arena.var(symbol);
    let three = arena.bv_const(8, 3).unwrap();
    let seven = arena.bv_const(8, 7).unwrap();
    let base = arena.eq(variable, three).unwrap();
    let contradiction = arena.eq(variable, seven).unwrap();
    (arena, base, contradiction)
}
