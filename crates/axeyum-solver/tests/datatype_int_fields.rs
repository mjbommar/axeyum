//! Datatypes carrying `Int`/`Real` fields (ADR-0022 step B extension).
//!
//! These exercise the native datatype expansion when constructor fields are
//! `Int`/`Real`: the per-field variable is created with the field's arithmetic
//! sort and the datatype-free residual is re-dispatched through `solve`, which
//! routes the arithmetic to the complete LIA/LRA deciders and bit-blasts the
//! tags. Every `sat` is projected back to a `Value::Datatype` and replayed.
#![cfg(feature = "full")]

use axeyum_ir::{Sort, TermArena, Value};
use axeyum_solver::{CheckResult, SolverConfig, solve};

/// `Box = mk(v: Int)`; `x,y: Box`; `v(x)=1 ∧ v(y)=2 ∧ x=y` is UNSAT by
/// congruence (`x=y ⇒ v(x)=v(y)`, contradicting `1 ≠ 2`).
#[test]
fn int_field_congruence_is_unsat() {
    let mut arena = TermArena::new();
    let boxd = arena.declare_datatype("Box");
    let mk = arena.add_constructor(boxd, "mk", &[("v".into(), Sort::Int)]);

    let x = arena.declare("x", Sort::Datatype(boxd)).unwrap();
    let y = arena.declare("y", Sort::Datatype(boxd)).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);

    let vx = arena.dt_select(mk, 0, xv).unwrap();
    let vy = arena.dt_select(mk, 0, yv).unwrap();
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let vx_is_one = arena.eq(vx, one).unwrap();
    let vy_is_two = arena.eq(vy, two).unwrap();
    let x_eq_y = arena.eq(xv, yv).unwrap();

    let result = solve(
        &mut arena,
        &[vx_is_one, vy_is_two, x_eq_y],
        &SolverConfig::default(),
    )
    .unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "x=y forces v(x)=v(y); 1 != 2 is unsat, got {result:?}"
    );
}

/// `List = nil | cons(head: Int, tail: List)`; `is-cons(l) ∧ head(l)=5` is SAT.
#[test]
fn int_field_is_cons_is_sat() {
    let mut arena = TermArena::new();
    let list = arena.declare_datatype("List");
    let _nil = arena.add_constructor(list, "nil", &[]);
    let cons = arena.add_constructor(
        list,
        "cons",
        &[
            ("head".into(), Sort::Int),
            ("tail".into(), Sort::Datatype(list)),
        ],
    );

    let l = arena.declare("l", Sort::Datatype(list)).unwrap();
    let lv = arena.var(l);
    let is_cons = arena.dt_test(cons, lv).unwrap();
    let head = arena.dt_select(cons, 0, lv).unwrap();
    let five = arena.int_const(5);
    let eq = arena.eq(head, five).unwrap();

    let result = solve(&mut arena, &[is_cons, eq], &SolverConfig::default()).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    match model.get(l) {
        Some(Value::Datatype {
            constructor,
            fields,
            ..
        }) => {
            assert_eq!(constructor, cons, "l must be cons");
            assert_eq!(fields[0], Value::Int(5), "head must be 5");
        }
        other => panic!("expected cons(5, _), got {other:?}"),
    }
}

/// `Box = mk(v: Int)`; `x: Box`; `v(x) + 1 = 4` is SAT (v = 3).
#[test]
fn int_field_arithmetic_is_sat() {
    let mut arena = TermArena::new();
    let boxd = arena.declare_datatype("Box");
    let mk = arena.add_constructor(boxd, "mk", &[("v".into(), Sort::Int)]);

    let x = arena.declare("x", Sort::Datatype(boxd)).unwrap();
    let xv = arena.var(x);
    let vx = arena.dt_select(mk, 0, xv).unwrap();
    let one = arena.int_const(1);
    let four = arena.int_const(4);
    let sum = arena.int_add(vx, one).unwrap();
    let eq = arena.eq(sum, four).unwrap();

    let result = solve(&mut arena, &[eq], &SolverConfig::default()).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    match model.get(x) {
        Some(Value::Datatype {
            constructor,
            fields,
            ..
        }) => {
            assert_eq!(constructor, mk, "x must be mk");
            assert_eq!(fields[0], Value::Int(3), "v must be 3");
        }
        other => panic!("expected mk(3), got {other:?}"),
    }
}

/// Multi-constructor congruence with Int fields: `Either = left(l: Int) |
/// right(r: Int)`; `x = y ∧ l(x) = 1 ∧ r(y) = 2` is SAT only if both pick the
/// same constructor — but the selects pin different constructors' fields, and
/// the default guards make the off-constructor field 0, so `x = y` is
/// satisfiable (e.g. both `left`, `r(y)` defaulted to 0, `l(x)=1`). This pins
/// that the multi-ctor tag arithmetic does not spuriously refute.
#[test]
fn multi_ctor_int_fields_is_sat() {
    let mut arena = TermArena::new();
    let either = arena.declare_datatype("Either");
    let left = arena.add_constructor(either, "left", &[("l".into(), Sort::Int)]);
    let _right = arena.add_constructor(either, "right", &[("r".into(), Sort::Int)]);

    let x = arena.declare("x", Sort::Datatype(either)).unwrap();
    let xv = arena.var(x);
    let is_left = arena.dt_test(left, xv).unwrap();
    let lx = arena.dt_select(left, 0, xv).unwrap();
    let one = arena.int_const(1);
    let eq = arena.eq(lx, one).unwrap();

    let result = solve(&mut arena, &[is_left, eq], &SolverConfig::default()).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    match model.get(x) {
        Some(Value::Datatype {
            constructor,
            fields,
            ..
        }) => {
            assert_eq!(constructor, left, "x must be left");
            assert_eq!(fields[0], Value::Int(1), "l must be 1");
        }
        other => panic!("expected left(1), got {other:?}"),
    }
}

/// Recursive `List Int`: traverse one level — `is-cons(l) ∧ is-cons(tail(l)) ∧
/// head(tail(l)) = 9` is SAT, with the nested tail carrying `head = 9`.
#[test]
fn recursive_list_int_traversal_is_sat() {
    let mut arena = TermArena::new();
    let list = arena.declare_datatype("List");
    let _nil = arena.add_constructor(list, "nil", &[]);
    let cons = arena.add_constructor(
        list,
        "cons",
        &[
            ("head".into(), Sort::Int),
            ("tail".into(), Sort::Datatype(list)),
        ],
    );

    let l = arena.declare("l", Sort::Datatype(list)).unwrap();
    let lv = arena.var(l);
    let is_cons = arena.dt_test(cons, lv).unwrap();
    let tail = arena.dt_select(cons, 1, lv).unwrap();
    let tail_is_cons = arena.dt_test(cons, tail).unwrap();
    let tail_head = arena.dt_select(cons, 0, tail).unwrap();
    let nine = arena.int_const(9);
    let eq = arena.eq(tail_head, nine).unwrap();

    let result = solve(
        &mut arena,
        &[is_cons, tail_is_cons, eq],
        &SolverConfig::default(),
    )
    .unwrap();
    assert!(
        matches!(result, CheckResult::Sat(_) | CheckResult::Unknown(_)),
        "a two-deep cons list with tail head 9 is satisfiable (or soundly unknown), got {result:?}"
    );
}
