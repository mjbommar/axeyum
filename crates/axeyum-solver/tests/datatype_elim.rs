//! End-to-end datatype solving via read-over-construct elimination (ADR-0022).

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, check_with_datatype_elimination};

fn pair_sort(arena: &mut TermArena) -> (axeyum_ir::ConstructorId, TermId, TermId) {
    let pair = arena.declare_datatype("Pair");
    let mk = arena.add_constructor(
        pair,
        "mk",
        &[("a".into(), Sort::BitVec(8)), ("b".into(), Sort::BitVec(8))],
    );
    let xs = arena.declare("x", Sort::BitVec(8)).unwrap();
    let ys = arena.declare("y", Sort::BitVec(8)).unwrap();
    (mk, arena.var(xs), arena.var(ys))
}

#[test]
fn select_field_constraint_is_sat() {
    // select_a(mk(x,y)) == 5  ->  x == 5  -> sat.
    let mut arena = TermArena::new();
    let (mk, x, y) = pair_sort(&mut arena);
    let p = arena.construct(mk, &[x, y]).unwrap();
    let sel = arena.dt_select(mk, 0, p).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let eq = arena.eq(sel, five).unwrap();
    assert!(matches!(
        check_with_datatype_elimination(&mut arena, &[eq], &SolverConfig::default()),
        Ok(CheckResult::Sat(_))
    ));
}

#[test]
fn conflicting_field_constraints_are_unsat() {
    // select_a(mk(x,y)) == 5 AND x == 3  ->  x == 5 AND x == 3 -> unsat.
    let mut arena = TermArena::new();
    let (mk, x, y) = pair_sort(&mut arena);
    let p = arena.construct(mk, &[x, y]).unwrap();
    let sel = arena.dt_select(mk, 0, p).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let three = arena.bv_const(8, 3).unwrap();
    let c1 = arena.eq(sel, five).unwrap();
    let c2 = arena.eq(x, three).unwrap();
    assert!(matches!(
        check_with_datatype_elimination(&mut arena, &[c1, c2], &SolverConfig::default()),
        Ok(CheckResult::Unsat)
    ));
}

#[test]
fn free_datatype_variable_is_unsupported() {
    // A bare datatype variable can't be eliminated -> Unsupported (needs a
    // native datatype theory).
    let mut arena = TermArena::new();
    let opt = arena.declare_datatype("Option");
    let _none = arena.add_constructor(opt, "none", &[]);
    let some = arena.add_constructor(opt, "some", &[("v".into(), Sort::BitVec(8))]);
    let os = arena.declare("o", Sort::Datatype(opt)).unwrap();
    let o = arena.var(os);
    let is_some = arena.dt_test(some, o).unwrap();
    assert!(matches!(
        check_with_datatype_elimination(&mut arena, &[is_some], &SolverConfig::default()),
        Err(axeyum_solver::SolverError::Unsupported(_))
    ));
}
