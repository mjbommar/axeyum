//! Finite product datatypes (records) lowered to bit-vectors.
#![cfg(feature = "full")]

use axeyum_ir::{Assignment, TermArena, Value, eval};
use axeyum_solver::{CheckResult, RecordSort, SolverConfig, solve};

#[test]
fn construct_then_select_returns_the_field() {
    // Point { x: BV8, y: BV8 } -> BV16; select-after-construct is the field.
    let point = RecordSort::new("Point", [("x", 8u32), ("y", 8u32)]).unwrap();
    assert_eq!(point.total_width(), 16);

    let mut arena = TermArena::new();
    let five = arena.bv_const(8, 5).unwrap();
    let seven = arena.bv_const(8, 7).unwrap();
    let p = point.construct(&mut arena, &[five, seven]).unwrap();
    let px = point.select(&mut arena, p, "x").unwrap();
    let py = point.select(&mut arena, p, "y").unwrap();

    let empty = Assignment::new();
    assert_eq!(
        eval(&arena, px, &empty).unwrap(),
        Value::Bv { width: 8, value: 5 }
    );
    assert_eq!(
        eval(&arena, py, &empty).unwrap(),
        Value::Bv { width: 8, value: 7 }
    );
}

#[test]
fn field_constraints_solve_and_replay() {
    let point = RecordSort::new("Point", [("x", 8u32), ("y", 8u32)]).unwrap();
    let mut arena = TermArena::new();
    let p = point.var(&mut arena, "p").unwrap();
    let px = point.select(&mut arena, p, "x").unwrap();
    let py = point.select(&mut arena, p, "y").unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let seven = arena.bv_const(8, 7).unwrap();
    let cx = arena.eq(px, five).unwrap();
    let cy = arena.eq(py, seven).unwrap();

    match solve(&mut arena, &[cx, cy], &SolverConfig::default()).unwrap() {
        CheckResult::Sat(model) => {
            let assignment = model.to_assignment();
            // The selected fields take the constrained values in the model.
            assert_eq!(
                eval(&arena, px, &assignment).unwrap(),
                Value::Bv { width: 8, value: 5 }
            );
            assert_eq!(
                eval(&arena, py, &assignment).unwrap(),
                Value::Bv { width: 8, value: 7 }
            );
        }
        other => panic!("expected sat, got {other:?}"),
    }
}

#[test]
fn distinct_field_constraints_can_be_unsat() {
    // select-x(p) == 5 AND select-x(p) == 6 -> unsat (same field, two values).
    let point = RecordSort::new("Point", [("x", 8u32), ("y", 8u32)]).unwrap();
    let mut arena = TermArena::new();
    let p = point.var(&mut arena, "p").unwrap();
    let px = point.select(&mut arena, p, "x").unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let six = arena.bv_const(8, 6).unwrap();
    let c1 = arena.eq(px, five).unwrap();
    let c2 = arena.eq(px, six).unwrap();

    assert!(matches!(
        solve(&mut arena, &[c1, c2], &SolverConfig::default()),
        Ok(CheckResult::Unsat)
    ));
}

#[test]
fn unknown_field_and_arity_are_errors() {
    let point = RecordSort::new("Point", [("x", 8u32), ("y", 8u32)]).unwrap();
    let mut arena = TermArena::new();
    let p = point.var(&mut arena, "p").unwrap();
    assert!(point.select(&mut arena, p, "z").is_err());
    let five = arena.bv_const(8, 5).unwrap();
    assert!(
        point.construct(&mut arena, &[five]).is_err(),
        "arity mismatch"
    );
}
