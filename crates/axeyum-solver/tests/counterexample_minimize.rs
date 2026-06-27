//! Public counterexample/model minimization API tests.

use axeyum_ir::{Sort, TermArena, Value, eval};
use axeyum_solver::{ModelMinimizeOutcome, SatBvBackend, Solver, SolverError, minimize_model};

fn expect_minimized(outcome: ModelMinimizeOutcome) -> axeyum_solver::Model {
    match outcome {
        ModelMinimizeOutcome::Minimized(model) => model,
        other => panic!("expected minimized model, got {other:?}"),
    }
}

#[test]
fn minimizes_bool_then_bv_in_requested_order() {
    let mut arena = TermArena::new();
    let flag_s = arena.declare("flag", Sort::Bool).unwrap();
    let x_s = arena.declare("x", Sort::BitVec(8)).unwrap();
    let flag = arena.var(flag_s);
    let x = arena.var(x_s);
    let seven = arena.bv_const(8, 7).unwrap();
    let ten = arena.bv_const(8, 10).unwrap();
    let x_ge_7 = arena.bv_uge(x, seven).unwrap();
    let flag_or_x_ge_7 = arena.or(flag, x_ge_7).unwrap();
    let x_le_10 = arena.bv_ule(x, ten).unwrap();

    let model = expect_minimized(
        minimize_model(&mut arena, &[flag_or_x_ge_7, x_le_10], &[flag_s, x_s]).unwrap(),
    );
    assert_eq!(model.get(flag_s), Some(Value::Bool(false)));
    assert_eq!(model.get(x_s), Some(Value::Bv { width: 8, value: 7 }));

    let assignment = model.to_assignment();
    assert_eq!(
        eval(&arena, flag_or_x_ge_7, &assignment).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval(&arena, x_le_10, &assignment).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn minimizes_int_symbol() {
    let mut arena = TermArena::new();
    let x_s = arena.declare("ix", Sort::Int).unwrap();
    let x = arena.var(x_s);
    let lo = arena.int_const(-3);
    let hi = arena.int_const(5);
    let x_ge_lo = arena.int_ge(x, lo).unwrap();
    let x_le_hi = arena.int_le(x, hi).unwrap();

    let model = expect_minimized(minimize_model(&mut arena, &[x_ge_lo, x_le_hi], &[x_s]).unwrap());
    assert_eq!(model.get(x_s), Some(Value::Int(-3)));
}

#[test]
fn solver_facade_minimizes_active_assertions() {
    let mut arena = TermArena::new();
    let x_s = arena.declare("sx", Sort::BitVec(4)).unwrap();
    let x = arena.var(x_s);
    let five = arena.bv_const(4, 5).unwrap();
    let eight = arena.bv_const(4, 8).unwrap();
    let x_ge_5 = arena.bv_uge(x, five).unwrap();
    let x_le_8 = arena.bv_ule(x, eight).unwrap();

    let mut solver = Solver::new(SatBvBackend::new());
    solver.assert(x_ge_5);
    solver.assert(x_le_8);

    let model = expect_minimized(solver.minimize_model(&mut arena, &[x_s]).unwrap());
    assert_eq!(model.get(x_s), Some(Value::Bv { width: 4, value: 5 }));
}

#[test]
fn infeasible_query_has_no_minimized_model() {
    let mut arena = TermArena::new();
    let x_s = arena.declare("bad_x", Sort::BitVec(2)).unwrap();
    let x = arena.var(x_s);
    let zero = arena.bv_const(2, 0).unwrap();
    let one = arena.bv_const(2, 1).unwrap();
    let x_eq_0 = arena.eq(x, zero).unwrap();
    let x_eq_1 = arena.eq(x, one).unwrap();

    assert_eq!(
        minimize_model(&mut arena, &[x_eq_0, x_eq_1], &[x_s]).unwrap(),
        ModelMinimizeOutcome::Infeasible
    );
}

#[test]
fn wide_bv_minimization_is_explicitly_unsupported() {
    let mut arena = TermArena::new();
    let x_s = arena.declare("wide", Sort::BitVec(128)).unwrap();
    let err = minimize_model(&mut arena, &[], &[x_s]).expect_err("BV128 is outside i128 result");
    match err {
        SolverError::Unsupported(detail) => {
            assert!(
                detail.contains("exceeds 127"),
                "unexpected detail: {detail}"
            );
        }
        other => panic!("expected unsupported, got {other:?}"),
    }
}
