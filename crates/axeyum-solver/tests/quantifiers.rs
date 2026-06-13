//! End-to-end quantifier solving by finite-domain expansion (ADR-0016).
//!
//! [`check_with_quantifiers`] expands each finite-domain quantifier to its
//! instances, dispatches the quantifier-free result, and replays the original
//! quantified formula through the enumerating evaluator.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, SolverError, check_with_quantifiers};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

fn solve(arena: &mut TermArena, assertions: &[axeyum_ir::TermId]) -> CheckResult {
    check_with_quantifiers(arena, assertions, &config())
        .expect("supported quantified query decides without error")
}

#[test]
fn universally_quantified_tautology_is_sat() {
    // forall x:BV4. x | x == x  is valid; asserting it is satisfiable.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(4)).unwrap();
    let x = arena.var(x_sym);
    let or = arena.bv_or(x, x).unwrap();
    let body = arena.eq(or, x).unwrap();
    let all = arena.forall(x_sym, body).unwrap();
    assert!(matches!(solve(&mut arena, &[all]), CheckResult::Sat(_)));
}

#[test]
fn false_universal_is_unsat() {
    // forall x:BV3. x == 0  is false, so asserting it is unsat.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(3)).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.bv_const(3, 0).unwrap();
    let body = arena.eq(x, zero).unwrap();
    let all = arena.forall(x_sym, body).unwrap();
    assert_eq!(solve(&mut arena, &[all]), CheckResult::Unsat);
}

#[test]
fn existential_with_free_variable_constrains_it() {
    // (exists x:BV4. x + y == 0) is valid for every y, but combined with a free
    // constraint on y the model must satisfy both. Here: y == 5 and
    // exists x. x + y == 3  (some x always works) — sat with y = 5.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(4)).unwrap();
    let y_sym = arena.declare("y", Sort::BitVec(4)).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let three = arena.bv_const(4, 3).unwrap();
    let five = arena.bv_const(4, 5).unwrap();
    let sum = arena.bv_add(x, y).unwrap();
    let inner = arena.eq(sum, three).unwrap();
    let some = arena.exists(x_sym, inner).unwrap();
    let y_is_5 = arena.eq(y, five).unwrap();

    let CheckResult::Sat(model) = solve(&mut arena, &[some, y_is_5]) else {
        panic!("expected sat");
    };
    assert_eq!(model.get(y_sym), Some(Value::Bv { width: 4, value: 5 }));
    // The original quantified formula replays true under the model.
    let assignment = model.to_assignment();
    assert_eq!(eval(&arena, some, &assignment).unwrap(), Value::Bool(true));
}

#[test]
fn nested_quantifier_decides() {
    // forall x:BV2. exists y:BV2. x == y  is valid → sat.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(2)).unwrap();
    let y_sym = arena.declare("y", Sort::BitVec(2)).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let eq = arena.eq(x, y).unwrap();
    let inner = arena.exists(y_sym, eq).unwrap();
    let outer = arena.forall(x_sym, inner).unwrap();
    assert!(matches!(solve(&mut arena, &[outer]), CheckResult::Sat(_)));
}

#[test]
fn quantifier_over_infinite_domain_is_unsupported() {
    let mut arena = TermArena::new();
    let r_sym = arena.declare("r", Sort::Real).unwrap();
    let r = arena.var(r_sym);
    let zero = arena.real_ratio(0, 1);
    let ge = arena.real_ge(r, zero).unwrap();
    let all = arena.forall(r_sym, ge).unwrap();
    assert!(matches!(
        check_with_quantifiers(&mut arena, &[all], &config()),
        Err(SolverError::Unsupported(_))
    ));
}
