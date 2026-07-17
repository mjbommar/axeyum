//! Native datatype solving for free variables: eager tag/field expansion with
//! model projection (ADR-0022 step B).
#![cfg(feature = "full")]

use axeyum_ir::{Sort, TermArena, Value};
use axeyum_solver::{CheckResult, SolverConfig, check_with_datatype_native};

/// Builds `Option = none | some(v: BitVec(8))` and returns (arena, opt, none,
/// some) ready for assertions.
fn option_arena() -> (
    TermArena,
    axeyum_ir::DatatypeId,
    axeyum_ir::ConstructorId,
    axeyum_ir::ConstructorId,
) {
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
            constructor,
            fields,
            ..
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
fn datatype_equality_with_conflicting_testers_is_unsat() {
    // o == o' AND is-some(o) AND is-none(o'): equal values cannot have different
    // constructors -> unsat.
    let (mut arena, opt, none, some) = option_arena();
    let o = arena.declare("o", Sort::Datatype(opt)).unwrap();
    let p = arena.declare("p", Sort::Datatype(opt)).unwrap();
    let ov = arena.var(o);
    let pv = arena.var(p);
    let eq = arena.eq(ov, pv).unwrap();
    let is_some_o = arena.dt_test(some, ov).unwrap();
    let is_none_p = arena.dt_test(none, pv).unwrap();

    let result = check_with_datatype_native(
        &mut arena,
        &[eq, is_some_o, is_none_p],
        &SolverConfig::default(),
    )
    .unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "equal values with different constructors must be unsat, got {result:?}"
    );
}

#[test]
fn datatype_equality_forces_field_agreement_unsat() {
    // o == p AND select v(o) == 7 AND select v(p) == 8 (both some): equality
    // forces the fields equal, so 7 == 8 -> unsat.
    let (mut arena, opt, _none, some) = option_arena();
    let o = arena.declare("o", Sort::Datatype(opt)).unwrap();
    let p = arena.declare("p", Sort::Datatype(opt)).unwrap();
    let ov = arena.var(o);
    let pv = arena.var(p);
    let eq = arena.eq(ov, pv).unwrap();
    let is_some_o = arena.dt_test(some, ov).unwrap();
    let is_some_p = arena.dt_test(some, pv).unwrap();
    let sel_o = arena.dt_select(some, 0, ov).unwrap();
    let sel_p = arena.dt_select(some, 0, pv).unwrap();
    let seven = arena.bv_const(8, 7).unwrap();
    let eight = arena.bv_const(8, 8).unwrap();
    let eo = arena.eq(sel_o, seven).unwrap();
    let ep = arena.eq(sel_p, eight).unwrap();

    let result = check_with_datatype_native(
        &mut arena,
        &[eq, is_some_o, is_some_p, eo, ep],
        &SolverConfig::default(),
    )
    .unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "equality forcing 7 == 8 must be unsat, got {result:?}"
    );
}

#[test]
fn datatype_equality_is_sat_with_matching_values() {
    // o == p AND select v(o) == 7 (both some): sat, with o and p both some(7).
    let (mut arena, opt, _none, some) = option_arena();
    let o = arena.declare("o", Sort::Datatype(opt)).unwrap();
    let p = arena.declare("p", Sort::Datatype(opt)).unwrap();
    let ov = arena.var(o);
    let pv = arena.var(p);
    let eq = arena.eq(ov, pv).unwrap();
    let is_some_o = arena.dt_test(some, ov).unwrap();
    let sel_o = arena.dt_select(some, 0, ov).unwrap();
    let seven = arena.bv_const(8, 7).unwrap();
    let eo = arena.eq(sel_o, seven).unwrap();

    let result =
        check_with_datatype_native(&mut arena, &[eq, is_some_o, eo], &SolverConfig::default())
            .unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    // Both variables project to some(7).
    for sym in [o, p] {
        match model.get(sym) {
            Some(Value::Datatype {
                constructor,
                fields,
                ..
            }) => {
                assert_eq!(constructor, some);
                assert_eq!(fields, vec![Value::Bv { width: 8, value: 7 }]);
            }
            other => panic!("expected some(7), got {other:?}"),
        }
    }
}

/// Builds `IntList = nil | cons(head: BitVec(8), tail: IntList)` and returns
/// (arena, list, nil, cons).
fn list_arena() -> (
    TermArena,
    axeyum_ir::DatatypeId,
    axeyum_ir::ConstructorId,
    axeyum_ir::ConstructorId,
) {
    let mut arena = TermArena::new();
    let list = arena.declare_datatype("IntList");
    let nil = arena.add_constructor(list, "nil", &[]);
    let cons = arena.add_constructor(
        list,
        "cons",
        &[
            ("head".into(), Sort::BitVec(8)),
            ("tail".into(), Sort::Datatype(list)),
        ],
    );
    (arena, list, nil, cons)
}

#[test]
fn recursive_datatype_tester_is_sat_with_defaulted_tail() {
    // is-cons(l) over a recursive list: sat. The (untraversed) tail field is
    // projected to its well-founded default `nil`, so l = cons(0, nil).
    let (mut arena, list, nil, cons) = list_arena();
    let l = arena.declare("l", Sort::Datatype(list)).unwrap();
    let lv = arena.var(l);
    let is_cons = arena.dt_test(cons, lv).unwrap();

    let result =
        check_with_datatype_native(&mut arena, &[is_cons], &SolverConfig::default()).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    match model.get(l) {
        Some(Value::Datatype {
            constructor,
            fields,
            ..
        }) => {
            assert_eq!(constructor, cons, "l must be a cons cell");
            assert_eq!(fields.len(), 2, "cons has head + tail");
            // The tail defaults to nil (the well-founded base).
            match &fields[1] {
                Value::Datatype { constructor, .. } => {
                    assert_eq!(*constructor, nil, "defaulted tail is nil");
                }
                other => panic!("expected datatype tail, got {other:?}"),
            }
        }
        other => panic!("expected a cons value, got {other:?}"),
    }
}

#[test]
fn recursive_datatype_scalar_field_constraint_is_sat() {
    // is-cons(l) AND select head(l) == 5: the *scalar* field is constrained;
    // sat with l = cons(5, nil). (The datatype tail is still untraversed.)
    let (mut arena, list, _nil, cons) = list_arena();
    let l = arena.declare("l", Sort::Datatype(list)).unwrap();
    let lv = arena.var(l);
    let is_cons = arena.dt_test(cons, lv).unwrap();
    let head = arena.dt_select(cons, 0, lv).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let eq = arena.eq(head, five).unwrap();

    let result =
        check_with_datatype_native(&mut arena, &[is_cons, eq], &SolverConfig::default()).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    match model.get(l) {
        Some(Value::Datatype { fields, .. }) => {
            assert_eq!(fields[0], Value::Bv { width: 8, value: 5 }, "head is 5");
        }
        other => panic!("expected a cons value, got {other:?}"),
    }
}

#[test]
fn recursive_datatype_contradictory_testers_are_unsat() {
    // is-cons(l) AND is-nil(l): sound unsat — the tag cannot be both, and the
    // (untraversed) tail does not affect this, so unsat is sound (no unfolding).
    let (mut arena, list, nil, cons) = list_arena();
    let l = arena.declare("l", Sort::Datatype(list)).unwrap();
    let lv = arena.var(l);
    let is_cons = arena.dt_test(cons, lv).unwrap();
    let is_nil = arena.dt_test(nil, lv).unwrap();

    let result =
        check_with_datatype_native(&mut arena, &[is_cons, is_nil], &SolverConfig::default())
            .unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "contradictory testers on a recursive list must be unsat, got {result:?}"
    );
}

#[test]
fn traversing_a_datatype_field_is_sat() {
    // is-cons(l) AND is-nil(tail(l)): traverses into the tail -> sat, with
    // l = cons(_, nil).
    let (mut arena, list, nil, cons) = list_arena();
    let l = arena.declare("l", Sort::Datatype(list)).unwrap();
    let lv = arena.var(l);
    let is_cons = arena.dt_test(cons, lv).unwrap();
    let tail = arena.dt_select(cons, 1, lv).unwrap();
    let tail_is_nil = arena.dt_test(nil, tail).unwrap();

    let result = check_with_datatype_native(
        &mut arena,
        &[is_cons, tail_is_nil],
        &SolverConfig::default(),
    )
    .unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    match model.get(l) {
        Some(Value::Datatype {
            constructor,
            fields,
            ..
        }) => {
            assert_eq!(constructor, cons);
            match &fields[1] {
                Value::Datatype { constructor, .. } => assert_eq!(*constructor, nil),
                other => panic!("expected nil tail, got {other:?}"),
            }
        }
        other => panic!("expected cons(_, nil), got {other:?}"),
    }
}

#[test]
fn traversal_requires_nondefault_tail_is_sat() {
    // is-cons(l) AND is-cons(tail(l)): the tail must be a *cons*, not the default
    // `nil`. This catches an over-constraining bug (which would wrongly report
    // unsat): l = cons(_, cons(_, nil)).
    let (mut arena, list, nil, cons) = list_arena();
    let l = arena.declare("l", Sort::Datatype(list)).unwrap();
    let lv = arena.var(l);
    let is_cons = arena.dt_test(cons, lv).unwrap();
    let tail = arena.dt_select(cons, 1, lv).unwrap();
    let tail_is_cons = arena.dt_test(cons, tail).unwrap();

    let result = check_with_datatype_native(
        &mut arena,
        &[is_cons, tail_is_cons],
        &SolverConfig::default(),
    )
    .unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected sat (tail can be a deeper cons), got {result:?}");
    };
    match model.get(l) {
        Some(Value::Datatype { fields, .. }) => match &fields[1] {
            Value::Datatype { constructor, .. } => {
                assert_eq!(
                    *constructor, cons,
                    "tail must be a cons, not the nil default"
                );
                let _ = nil;
            }
            other => panic!("expected cons tail, got {other:?}"),
        },
        other => panic!("expected a cons value, got {other:?}"),
    }
}

#[test]
fn contradictory_testers_on_a_traversed_field_are_unsat() {
    // is-cons(tail(l)) AND is-nil(tail(l)): the tail cannot be both -> sound
    // unsat (the relaxation preserves unsat soundness).
    let (mut arena, list, nil, cons) = list_arena();
    let l = arena.declare("l", Sort::Datatype(list)).unwrap();
    let lv = arena.var(l);
    let tail = arena.dt_select(cons, 1, lv).unwrap();
    let tail_is_cons = arena.dt_test(cons, tail).unwrap();
    let tail_is_nil = arena.dt_test(nil, tail).unwrap();

    let result = check_with_datatype_native(
        &mut arena,
        &[tail_is_cons, tail_is_nil],
        &SolverConfig::default(),
    )
    .unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "contradictory testers on a traversed field must be unsat, got {result:?}"
    );
}

#[test]
fn nested_scalar_field_through_traversal_is_sat() {
    // is-cons(l) AND is-cons(tail(l)) AND select head(tail(l)) == 9: a scalar
    // field reached through a traversal -> sat with the nested head == 9.
    let (mut arena, list, _nil, cons) = list_arena();
    let l = arena.declare("l", Sort::Datatype(list)).unwrap();
    let lv = arena.var(l);
    let is_cons = arena.dt_test(cons, lv).unwrap();
    let tail = arena.dt_select(cons, 1, lv).unwrap();
    let tail_is_cons = arena.dt_test(cons, tail).unwrap();
    let nested_head = arena.dt_select(cons, 0, tail).unwrap();
    let nine = arena.bv_const(8, 9).unwrap();
    let eq = arena.eq(nested_head, nine).unwrap();

    let result = check_with_datatype_native(
        &mut arena,
        &[is_cons, tail_is_cons, eq],
        &SolverConfig::default(),
    )
    .unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    match model.get(l) {
        Some(Value::Datatype { fields, .. }) => match &fields[1] {
            Value::Datatype {
                fields: tfields, ..
            } => {
                assert_eq!(
                    tfields[0],
                    Value::Bv { width: 8, value: 9 },
                    "nested head is 9"
                );
            }
            other => panic!("expected cons tail, got {other:?}"),
        },
        other => panic!("expected a cons value, got {other:?}"),
    }
}

#[test]
fn recursive_equality_with_conflicting_testers_is_unsat() {
    // l == m AND is-cons(l) AND is-nil(m): equality forces the tags equal, but
    // the testers force them different -> sound unsat (equality over a datatype
    // with datatype fields, reduced on tag + scalar fields).
    let (mut arena, list, nil, cons) = list_arena();
    let l = arena.declare("l", Sort::Datatype(list)).unwrap();
    let m = arena.declare("m", Sort::Datatype(list)).unwrap();
    let lv = arena.var(l);
    let mv = arena.var(m);
    let eq = arena.eq(lv, mv).unwrap();
    let is_cons_l = arena.dt_test(cons, lv).unwrap();
    let is_nil_m = arena.dt_test(nil, mv).unwrap();

    let result = check_with_datatype_native(
        &mut arena,
        &[eq, is_cons_l, is_nil_m],
        &SolverConfig::default(),
    )
    .unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "recursive equality with conflicting testers must be unsat, got {result:?}"
    );
}

#[test]
fn recursive_equality_forces_scalar_field_unsat() {
    // l == m AND is-cons(l) AND is-cons(m) AND head(l) == 5 AND head(m) == 6:
    // equality forces the cons heads equal, so 5 == 6 -> sound unsat.
    let (mut arena, list, _nil, cons) = list_arena();
    let l = arena.declare("l", Sort::Datatype(list)).unwrap();
    let m = arena.declare("m", Sort::Datatype(list)).unwrap();
    let lv = arena.var(l);
    let mv = arena.var(m);
    let eq = arena.eq(lv, mv).unwrap();
    let is_cons_l = arena.dt_test(cons, lv).unwrap();
    let is_cons_m = arena.dt_test(cons, mv).unwrap();
    let head_l = arena.dt_select(cons, 0, lv).unwrap();
    let head_m = arena.dt_select(cons, 0, mv).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let six = arena.bv_const(8, 6).unwrap();
    let e5 = arena.eq(head_l, five).unwrap();
    let e6 = arena.eq(head_m, six).unwrap();

    let result = check_with_datatype_native(
        &mut arena,
        &[eq, is_cons_l, is_cons_m, e5, e6],
        &SolverConfig::default(),
    )
    .unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "recursive equality forcing 5 == 6 must be unsat, got {result:?}"
    );
}

#[test]
fn recursive_equality_is_sat_with_defaulted_fields() {
    // l == m AND is-cons(l): sat — both project to cons(0, nil) (datatype tail
    // defaulted equally), so equality holds.
    let (mut arena, list, _nil, cons) = list_arena();
    let l = arena.declare("l", Sort::Datatype(list)).unwrap();
    let m = arena.declare("m", Sort::Datatype(list)).unwrap();
    let lv = arena.var(l);
    let mv = arena.var(m);
    let eq = arena.eq(lv, mv).unwrap();
    let is_cons_l = arena.dt_test(cons, lv).unwrap();

    let result =
        check_with_datatype_native(&mut arena, &[eq, is_cons_l], &SolverConfig::default()).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    // l and m project to the same value.
    assert_eq!(model.get(l), model.get(m), "l and m must be equal");
}

#[test]
fn mutually_recursive_datatypes_traverse_and_solve() {
    // Tree = leaf(lval: BitVec(8)) | branch(bforest: Forest)
    // Forest = fnil | fcons(fhead: Tree, ftail: Forest)
    // Traverse Tree -> Forest -> Tree: is-branch(t), the forest is fcons, its
    // head is a leaf with lval == 9. Sat with t = branch(fcons(leaf(9), fnil)).
    let mut arena = TermArena::new();
    let tree = arena.declare_datatype("Tree");
    let forest = arena.declare_datatype("Forest");
    let leaf = arena.add_constructor(tree, "leaf", &[("lval".into(), Sort::BitVec(8))]);
    let branch = arena.add_constructor(
        tree,
        "branch",
        &[("bforest".into(), Sort::Datatype(forest))],
    );
    let _fnil = arena.add_constructor(forest, "fnil", &[]);
    let fcons = arena.add_constructor(
        forest,
        "fcons",
        &[
            ("fhead".into(), Sort::Datatype(tree)),
            ("ftail".into(), Sort::Datatype(forest)),
        ],
    );

    let t = arena.declare("t", Sort::Datatype(tree)).unwrap();
    let tv = arena.var(t);
    let is_branch = arena.dt_test(branch, tv).unwrap(); // is-branch(t)
    let bf = arena.dt_select(branch, 0, tv).unwrap(); // bforest(t) : Forest
    let is_fcons = arena.dt_test(fcons, bf).unwrap(); // is-fcons(bforest(t))
    let fh = arena.dt_select(fcons, 0, bf).unwrap(); // fhead(...) : Tree
    let is_leaf = arena.dt_test(leaf, fh).unwrap(); // is-leaf(fhead(...))
    let lv = arena.dt_select(leaf, 0, fh).unwrap(); // lval(...) : BitVec(8)
    let nine = arena.bv_const(8, 9).unwrap();
    let eq = arena.eq(lv, nine).unwrap();

    let result = check_with_datatype_native(
        &mut arena,
        &[is_branch, is_fcons, is_leaf, eq],
        &SolverConfig::default(),
    )
    .unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    // t = branch(fcons(leaf(9), _))
    match model.get(t) {
        Some(Value::Datatype {
            constructor,
            fields,
            ..
        }) => {
            assert_eq!(constructor, branch, "t is a branch");
            let Value::Datatype { fields: f, .. } = &fields[0] else {
                panic!("bforest is a Forest value");
            };
            let Value::Datatype { fields: h, .. } = &f[0] else {
                panic!("fhead is a Tree value");
            };
            assert_eq!(h[0], Value::Bv { width: 8, value: 9 }, "nested lval is 9");
        }
        other => panic!("expected branch(...), got {other:?}"),
    }
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
