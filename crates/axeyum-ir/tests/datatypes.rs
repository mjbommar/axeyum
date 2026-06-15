//! First-class datatype sort: construct / select / test, including recursion
//! (ADR-0022). The ground evaluator is the semantic reference, so these tests
//! pin the datatype semantics that any future datatype solver must match.

use axeyum_ir::{Assignment, Sort, TermArena, Value, eval, well_founded_default};

#[test]
fn recursive_list_construct_select_test() {
    // IntList = nil | cons(head: BitVec(8), tail: IntList)
    let mut arena = TermArena::new();
    let list = arena.declare_datatype("IntList");
    let nil = arena.add_constructor(list, "nil", &[]);
    let cons = arena.add_constructor(
        list,
        "cons",
        &[
            ("head".to_string(), Sort::BitVec(8)),
            ("tail".to_string(), Sort::Datatype(list)),
        ],
    );

    let nil_t = arena.construct(nil, &[]).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let cons_t = arena.construct(cons, &[five, nil_t]).unwrap();

    // The constructed term has the datatype sort.
    assert_eq!(arena.sort_of(cons_t), Sort::Datatype(list));

    let a = Assignment::new();
    // Testers.
    let is_cons = arena.dt_test(cons, cons_t).unwrap();
    let is_nil = arena.dt_test(nil, cons_t).unwrap();
    assert_eq!(eval(&arena, is_cons, &a).unwrap(), Value::Bool(true));
    assert_eq!(eval(&arena, is_nil, &a).unwrap(), Value::Bool(false));

    // Selectors: head is 5, tail is nil.
    let head = arena.dt_select(cons, 0, cons_t).unwrap();
    assert_eq!(
        eval(&arena, head, &a).unwrap(),
        Value::Bv { width: 8, value: 5 }
    );
    let tail = arena.dt_select(cons, 1, cons_t).unwrap();
    let tail_is_nil = arena.dt_test(nil, tail).unwrap();
    assert_eq!(eval(&arena, tail_is_nil, &a).unwrap(), Value::Bool(true));
}

#[test]
fn well_founded_default_picks_a_base_constructor() {
    // A recursive list defaults to its base constructor `nil`, not the recursive
    // `cons` (which would not terminate). Constructor declaration order is
    // deliberately recursive-first to prove the search prefers the well-founded
    // case rather than the first constructor.
    let mut arena = TermArena::new();
    let list = arena.declare_datatype("IntList");
    let cons = arena.add_constructor(
        list,
        "cons",
        &[
            ("head".to_string(), Sort::BitVec(8)),
            ("tail".to_string(), Sort::Datatype(list)),
        ],
    );
    let nil = arena.add_constructor(list, "nil", &[]);
    let _ = cons;

    match well_founded_default(&arena, Sort::Datatype(list)) {
        Some(Value::Datatype {
            constructor,
            fields,
            ..
        }) => {
            assert_eq!(constructor, nil, "default list is the base constructor nil");
            assert!(fields.is_empty(), "nil has no fields");
        }
        other => panic!("expected a default list value, got {other:?}"),
    }
}

#[test]
fn well_founded_default_none_for_uninhabited_datatype() {
    // A datatype with only a recursive constructor (no base case) is uninhabited
    // -> no finite default value exists.
    let mut arena = TermArena::new();
    let stream = arena.declare_datatype("Stream");
    let _scons = arena.add_constructor(
        stream,
        "scons",
        &[
            ("head".to_string(), Sort::BitVec(8)),
            ("tail".to_string(), Sort::Datatype(stream)),
        ],
    );
    assert_eq!(
        well_founded_default(&arena, Sort::Datatype(stream)),
        None,
        "an uninhabited datatype has no well-founded default"
    );
}

#[test]
fn selector_on_wrong_constructor_returns_field_default() {
    // Selecting cons's `head` from a `nil` value is the chosen-total convention
    // (ADR-0022 step-B gate): it returns the well-founded default of the field's
    // sort (BitVec(8) -> 0), keeping `select` total so projected datatype models
    // replay soundly. (Previously this errored; totality is required for native
    // datatype solving's model projection.)
    let mut arena = TermArena::new();
    let list = arena.declare_datatype("IntList");
    let nil = arena.add_constructor(list, "nil", &[]);
    let cons = arena.add_constructor(
        list,
        "cons",
        &[
            ("head".to_string(), Sort::BitVec(8)),
            ("tail".to_string(), Sort::Datatype(list)),
        ],
    );
    let nil_t = arena.construct(nil, &[]).unwrap();
    let bad = arena.dt_select(cons, 0, nil_t).unwrap();
    let v = eval(&arena, bad, &Assignment::new()).expect("select is total");
    assert_eq!(
        v.as_bv(),
        Some((8, 0)),
        "wrong-constructor select returns the field's well-founded default"
    );
}

#[test]
fn datatype_symbol_binds_and_evaluates() {
    // Option = none | some(value: BitVec(8)); bind a symbol to some(7).
    let mut arena = TermArena::new();
    let opt = arena.declare_datatype("Option");
    let none = arena.add_constructor(opt, "none", &[]);
    let some = arena.add_constructor(opt, "some", &[("value".to_string(), Sort::BitVec(8))]);

    let x = arena.declare("x", Sort::Datatype(opt)).unwrap();
    let xv = arena.var(x);
    let is_some = arena.dt_test(some, xv).unwrap();
    let value = arena.dt_select(some, 0, xv).unwrap();

    let mut a = Assignment::new();
    a.set(
        x,
        Value::Datatype {
            datatype: opt,
            constructor: some,
            fields: vec![Value::Bv { width: 8, value: 7 }],
        },
    );
    assert_eq!(eval(&arena, is_some, &a).unwrap(), Value::Bool(true));
    let is_none = arena.dt_test(none, xv).unwrap();
    assert_eq!(eval(&arena, is_none, &a).unwrap(), Value::Bool(false));
    assert_eq!(
        eval(&arena, value, &a).unwrap(),
        Value::Bv { width: 8, value: 7 }
    );
}

#[test]
fn construct_checks_arity_and_field_sorts() {
    let mut arena = TermArena::new();
    let opt = arena.declare_datatype("Option");
    let some = arena.add_constructor(opt, "some", &[("value".to_string(), Sort::BitVec(8))]);
    // Wrong arity.
    assert!(arena.construct(some, &[]).is_err());
    // Wrong field sort (Bool instead of BitVec(8)).
    let b = arena.bool_const(true);
    assert!(arena.construct(some, &[b]).is_err());
}
