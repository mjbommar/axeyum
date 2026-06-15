//! Arithmetic (Int/Real) if-then-else via exact ite-lifting in `check_auto`.

use axeyum_ir::TermArena;
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn run(a: &mut TermArena, asserts: &[axeyum_ir::TermId]) -> CheckResult {
    solve(a, asserts, &SolverConfig::default()).expect("decides without error")
}

#[test]
fn int_ite_false_branch_contradiction_is_unsat() {
    // b = false AND ite(b, 1, -1) > 0 : the chosen branch is -1, so >0 is unsat.
    let mut a = TermArena::new();
    let b = a.bool_var("b").unwrap();
    let one = a.int_const(1);
    let neg1 = a.int_const(-1);
    let it = a.ite(b, one, neg1).unwrap();
    let zero = a.int_const(0);
    let gt = a.int_gt(it, zero).unwrap();
    let nb = a.not(b).unwrap();
    assert!(
        matches!(run(&mut a, &[nb, gt]), CheckResult::Unsat),
        "ite(false,1,-1)>0 unsat"
    );
}

#[test]
fn int_ite_is_sat_with_right_branch() {
    // x = ite(b, 10, 20) AND x == 20 : sat (b = false).
    let mut a = TermArena::new();
    let b = a.bool_var("b").unwrap();
    let x = a.int_var("x").unwrap();
    let ten = a.int_const(10);
    let twenty = a.int_const(20);
    let it = a.ite(b, ten, twenty).unwrap();
    let xe = a.eq(x, it).unwrap();
    let x20 = a.eq(x, twenty).unwrap();
    assert!(
        matches!(run(&mut a, &[xe, x20]), CheckResult::Sat(_)),
        "x=ite,x=20 sat"
    );
}

#[test]
fn real_ite_both_branches_force_unsat() {
    // ite(b, x, y) > 5 AND x <= 5 AND y <= 5 : whichever branch, <= 5, so unsat.
    let mut a = TermArena::new();
    let b = a.bool_var("b").unwrap();
    let x = a.real_var("x").unwrap();
    let y = a.real_var("y").unwrap();
    let it = a.ite(b, x, y).unwrap();
    let five = a.real_const(axeyum_ir::Rational::integer(5));
    let gt = a.real_gt(it, five).unwrap();
    let xle = a.real_le(x, five).unwrap();
    let yle = a.real_le(y, five).unwrap();
    assert!(
        matches!(run(&mut a, &[gt, xle, yle]), CheckResult::Unsat),
        "real ite > 5 unsat"
    );
}
