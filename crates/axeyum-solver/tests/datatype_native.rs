//! Native datatype solving for free variables: eager tag/field expansion with
//! model projection (ADR-0022 step B).

use axeyum_ir::{Sort, TermArena, Value};
use axeyum_solver::{CheckResult, SolverConfig, check_with_datatype_native};

/// Builds `Option = none | some(v: BitVec(8))` and returns (arena, opt, none,
/// some) ready for assertions.
fn option_arena() -> (TermArena, axeyum_ir::DatatypeId, axeyum_ir::ConstructorId, axeyum_ir::ConstructorId) {
    let mut arena = TermArena::new();
    let opt = arena.declare_datatype("Option");
    let none = arena.add_constructor(opt, "none", &[]);
    let some = arena.add_constructor(opt, "some", &[("v".into(), Sort::BitVec(8))]);
    (arena, opt, none, some)
}

#[test]
fn free_enum_variable_is_sat_with_projected_model() {
    // Color = red | green | blue; assert is-green(c). Expect sat with c = green.
    let mut arena = TermArena::new();
    let color = arena.declare_datatype("Color");
    let _red = arena.add_constructor(color, "red", &[]);
    let green = arena.add_constructor(color, "green", &[]);
    let _blue = arena.add_constructor(color, "blue", &[]);

    let c = arena.declare("c", Sort::Datatype(color)).unwrap();
    let cv = arena.var(c);
    let is_green = arena.dt_test(green, cv).unwrap();

    let result =
        check_with_datatype_native(&mut arena, &[is_green], &SolverConfig::default()).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    match model.get(c) {
        Some(Value::Datatype { constructor, .. }) => {
            assert_eq!(constructor, green, "c must be the green constructor");
        }
        other => panic!("expected a datatype model value, got {other:?}"),
    }
}

#[test]
fn free_variable_with_select_is_sat() {
    // is-some(o) AND select v(o) == 7  ->  sat with o = some(7).
    let (mut arena, opt, _none, some) = option_arena();
    let o = arena.declare("o", Sort::Datatype(opt)).unwrap();
    let ov = arena.var(o);
    let is_some = arena.dt_test(some, ov).unwrap();
    let sel = arena.dt_select(some, 0, ov).unwrap();
    let seven = arena.bv_const(8, 7).unwrap();
    let eq = arena.eq(sel, seven).unwrap();

    let result =
        check_with_datatype_native(&mut arena, &[is_some, eq], &SolverConfig::default()).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    match model.get(o) {
        Some(Value::Datatype {
            constructor, fields, ..
        }) => {
            assert_eq!(constructor, some, "o must be `some`");
            assert_eq!(fields, vec![Value::Bv { width: 8, value: 7 }], "field is 7");
        }
        other => panic!("expected `some(7)`, got {other:?}"),
    }
}

#[test]
fn contradictory_testers_are_unsat() {
    // is-some(o) AND is-none(o): the tag cannot be both -> unsat.
    let (mut arena, opt, none, some) = option_arena();
    let o = arena.declare("o", Sort::Datatype(opt)).unwrap();
    let ov = arena.var(o);
    let is_some = arena.dt_test(some, ov).unwrap();
    let is_none = arena.dt_test(none, ov).unwrap();

    let result =
        check_with_datatype_native(&mut arena, &[is_some, is_none], &SolverConfig::default())
            .unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "contradictory testers must be unsat, got {result:?}"
    );
}

#[test]
fn select_on_wrong_constructor_uses_default_sat() {
    // is-none(o) AND select v(o) == 0: selecting `some`'s field from a `none`
    // value yields the well-founded default (0) by the total convention, so this
    // is sat.
    let (mut arena, opt, none, some) = option_arena();
    let o = arena.declare("o", Sort::Datatype(opt)).unwrap();
    let ov = arena.var(o);
    let is_none = arena.dt_test(none, ov).unwrap();
    let sel = arena.dt_select(some, 0, ov).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let eq = arena.eq(sel, zero).unwrap();

    let result =
        check_with_datatype_native(&mut arena, &[is_none, eq], &SolverConfig::default()).unwrap();
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "wrong-ctor select == default must be sat, got {result:?}"
    );
}

#[test]
fn select_on_wrong_constructor_nonzero_is_unsat() {
    // is-none(o) AND select v(o) == 5: the default is 0, not 5 -> unsat.
    let (mut arena, opt, none, some) = option_arena();
    let o = arena.declare("o", Sort::Datatype(opt)).unwrap();
    let ov = arena.var(o);
    let is_none = arena.dt_test(none, ov).unwrap();
    let sel = arena.dt_select(some, 0, ov).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let eq = arena.eq(sel, five).unwrap();

    let result =
        check_with_datatype_native(&mut arena, &[is_none, eq], &SolverConfig::default()).unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "wrong-ctor select == non-default must be unsat, got {result:?}"
    );
}

#[test]
fn dispatcher_routes_datatype_queries() {
    // The high-level `solve` dispatcher should route a free-datatype query
    // through to the native path and return sat.
    let (mut arena, opt, _none, some) = option_arena();
    let o = arena.declare("o", Sort::Datatype(opt)).unwrap();
    let ov = arena.var(o);
    let is_some = arena.dt_test(some, ov).unwrap();

    let result = axeyum_solver::solve(&mut arena, &[is_some], &SolverConfig::default()).unwrap();
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "dispatcher must solve free-datatype queries, got {result:?}"
    );
}
