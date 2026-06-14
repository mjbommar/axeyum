//! Datatype read-over-construct simplification (ADR-0022).

use axeyum_ir::{Sort, TermArena};
use axeyum_rewrite::simplify_datatypes;

#[test]
fn select_over_construct_folds_to_field() {
    let mut arena = TermArena::new();
    let pair = arena.declare_datatype("Pair");
    let mk = arena.add_constructor(
        pair,
        "mk",
        &[("a".into(), Sort::BitVec(8)), ("b".into(), Sort::BitVec(8))],
    );
    let xs = arena.declare("x", Sort::BitVec(8)).unwrap();
    let ys = arena.declare("y", Sort::BitVec(8)).unwrap();
    let x = arena.var(xs);
    let y = arena.var(ys);
    let p = arena.construct(mk, &[x, y]).unwrap();
    let sel_a = arena.dt_select(mk, 0, p).unwrap();
    let sel_b = arena.dt_select(mk, 1, p).unwrap();

    let eq_a = arena.eq(sel_a, x).unwrap();
    let eq_b = arena.eq(sel_b, y).unwrap();
    let simplified = simplify_datatypes(&mut arena, &[eq_a, eq_b]).unwrap();

    // select_a(mk(x,y)) folds to x; select_b folds to y -> the assertions become
    // x == x and y == y (datatype-free).
    let xx = arena.eq(x, x).unwrap();
    let yy = arena.eq(y, y).unwrap();
    assert_eq!(simplified[0], xx, "select_a(mk(x,y)) should fold to x");
    assert_eq!(simplified[1], yy, "select_b(mk(x,y)) should fold to y");
}

#[test]
fn test_over_construct_folds_to_bool() {
    let mut arena = TermArena::new();
    let opt = arena.declare_datatype("Option");
    let none = arena.add_constructor(opt, "none", &[]);
    let some = arena.add_constructor(opt, "some", &[("v".into(), Sort::BitVec(8))]);
    let seven = arena.bv_const(8, 7).unwrap();
    let some7 = arena.construct(some, &[seven]).unwrap();

    let is_some = arena.dt_test(some, some7).unwrap();
    let is_none = arena.dt_test(none, some7).unwrap();
    let simplified = simplify_datatypes(&mut arena, &[is_some, is_none]).unwrap();

    let t = arena.bool_const(true);
    let f = arena.bool_const(false);
    assert_eq!(simplified[0], t, "is-some(some(7)) folds to true");
    assert_eq!(simplified[1], f, "is-none(some(7)) folds to false");
}
