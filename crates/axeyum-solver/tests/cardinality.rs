//! Cardinality constraints (at-most / at-least / exactly) over Booleans.

use axeyum_ir::{Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, at_least, at_most, exactly, solve};

fn bool_var(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::Bool).unwrap();
    arena.var(sym)
}

fn count_true(arena: &TermArena, bools: &[TermId], model: &axeyum_solver::Model) -> usize {
    let assignment = model.to_assignment();
    bools
        .iter()
        .filter(|&&b| eval(arena, b, &assignment).unwrap() == Value::Bool(true))
        .count()
}

#[test]
fn at_most_and_at_least_pin_the_count() {
    let mut arena = TermArena::new();
    let bs = [
        bool_var(&mut arena, "a"),
        bool_var(&mut arena, "b"),
        bool_var(&mut arena, "c"),
    ];
    let lo = at_least(&mut arena, &bs, 2).unwrap();
    let hi = at_most(&mut arena, &bs, 2).unwrap();
    match solve(&mut arena, &[lo, hi], &SolverConfig::default()).unwrap() {
        CheckResult::Sat(model) => assert_eq!(count_true(&arena, &bs, &model), 2),
        other => panic!("expected sat, got {other:?}"),
    }
}

#[test]
fn conflicting_bounds_are_unsat() {
    // at most 1 AND at least 2 cannot both hold.
    let mut arena = TermArena::new();
    let bs = [
        bool_var(&mut arena, "a"),
        bool_var(&mut arena, "b"),
        bool_var(&mut arena, "c"),
    ];
    let hi = at_most(&mut arena, &bs, 1).unwrap();
    let lo = at_least(&mut arena, &bs, 2).unwrap();
    assert!(matches!(
        solve(&mut arena, &[hi, lo], &SolverConfig::default()),
        Ok(CheckResult::Unsat)
    ));
}

#[test]
fn exactly_zero_forces_all_false() {
    // exactly 0 of {a,b,c} AND a  ->  unsat.
    let mut arena = TermArena::new();
    let a = bool_var(&mut arena, "a");
    let bs = [a, bool_var(&mut arena, "b"), bool_var(&mut arena, "c")];
    let none = exactly(&mut arena, &bs, 0).unwrap();
    assert!(matches!(
        solve(&mut arena, &[none, a], &SolverConfig::default()),
        Ok(CheckResult::Unsat)
    ));
}

#[test]
fn at_least_all_forces_every_true() {
    // at least 3 of 3  ->  all true.
    let mut arena = TermArena::new();
    let bs = [
        bool_var(&mut arena, "a"),
        bool_var(&mut arena, "b"),
        bool_var(&mut arena, "c"),
    ];
    let all = at_least(&mut arena, &bs, 3).unwrap();
    match solve(&mut arena, &[all], &SolverConfig::default()).unwrap() {
        CheckResult::Sat(model) => assert_eq!(count_true(&arena, &bs, &model), 3),
        other => panic!("expected sat, got {other:?}"),
    }
}
