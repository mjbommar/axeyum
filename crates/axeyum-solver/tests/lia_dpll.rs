//! Boolean-structured `QF_LIA` (disjunctions/implications of integer atoms) via
//! the lazy-SMT loop over the integer simplex, and through the dispatcher.

use axeyum_ir::{Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, check_with_lia_dpll, solve};

fn int_var(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::Int).unwrap();
    arena.var(sym)
}

#[test]
fn disjunction_is_satisfiable_and_replayed() {
    // (x < 0 OR x > 10) AND x == 15  ->  sat at x = 15.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let zero = arena.int_const(0);
    let ten = arena.int_const(10);
    let fifteen = arena.int_const(15);
    let lo = arena.int_lt(x, zero).unwrap();
    let hi = arena.int_gt(x, ten).unwrap();
    let disj = arena.or(lo, hi).unwrap();
    let pin = arena.eq(x, fifteen).unwrap();

    match check_with_lia_dpll(&mut arena, &[disj, pin], &SolverConfig::default()).unwrap() {
        CheckResult::Sat(model) => {
            let assignment = model.to_assignment();
            assert_eq!(eval(&arena, disj, &assignment).unwrap(), Value::Bool(true));
            assert_eq!(eval(&arena, pin, &assignment).unwrap(), Value::Bool(true));
        }
        other => panic!("expected sat, got {other:?}"),
    }
}

#[test]
fn disjunction_with_excluded_value_is_unsat() {
    // (x < 0 OR x > 10) AND x == 5 : 5 is neither < 0 nor > 10 -> unsat. This
    // needs the lazy loop to refute *both* disjuncts under x == 5.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let zero = arena.int_const(0);
    let ten = arena.int_const(10);
    let five = arena.int_const(5);
    let lo = arena.int_lt(x, zero).unwrap();
    let hi = arena.int_gt(x, ten).unwrap();
    let disj = arena.or(lo, hi).unwrap();
    let pin = arena.eq(x, five).unwrap();

    assert!(matches!(
        check_with_lia_dpll(&mut arena, &[disj, pin], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

#[test]
fn equality_disjunction_is_unsat_via_dispatcher() {
    // (x == 2 OR x == 4) AND x == 3 -> unsat, decided through the top-level
    // dispatcher (which routes Boolean-structured integer queries to the loop).
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let two = arena.int_const(2);
    let four = arena.int_const(4);
    let three = arena.int_const(3);
    let is2 = arena.eq(x, two).unwrap();
    let is4 = arena.eq(x, four).unwrap();
    let disj = arena.or(is2, is4).unwrap();
    let pin = arena.eq(x, three).unwrap();

    assert!(matches!(
        solve(&mut arena, &[disj, pin], &SolverConfig::default()),
        Ok(CheckResult::Unsat)
    ));
}

#[test]
fn implication_chain_is_satisfiable() {
    // (x > 5 => y > 10) AND x == 6 : sat, with y > 10 forced.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let y = int_var(&mut arena, "y");
    let five = arena.int_const(5);
    let ten = arena.int_const(10);
    let six = arena.int_const(6);
    let xgt5 = arena.int_gt(x, five).unwrap();
    let ygt10 = arena.int_gt(y, ten).unwrap();
    let imp = arena.implies(xgt5, ygt10).unwrap();
    let pin = arena.eq(x, six).unwrap();

    match solve(&mut arena, &[imp, pin], &SolverConfig::default()).unwrap() {
        CheckResult::Sat(model) => {
            let assignment = model.to_assignment();
            assert_eq!(eval(&arena, imp, &assignment).unwrap(), Value::Bool(true));
            assert_eq!(eval(&arena, pin, &assignment).unwrap(), Value::Bool(true));
        }
        other => panic!("expected sat, got {other:?}"),
    }
}
