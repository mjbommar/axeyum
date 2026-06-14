//! Bit-vector / integer coercions (`bv2nat` / `int2bv`) through the auto
//! dispatcher's combined bit-blasting path (arrays/funcs/integers to `QF_BV`).

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn solve_auto(arena: &mut TermArena, assertions: &[axeyum_ir::TermId]) -> CheckResult {
    solve(arena, assertions, &SolverConfig::default()).expect("decides without error")
}

#[test]
fn bv2nat_constraint_is_sat() {
    // bv2nat(x) == 200 with x : BitVec(8) -> sat (x = 0xc8); the Int and BV
    // sides share the value through the unified bit-blast.
    let mut a = TermArena::new();
    let x = a.bv_var("x", 8).unwrap();
    let n = a.bv2nat(x).unwrap();
    let target = a.int_const(200);
    let eq = a.eq(n, target).unwrap();
    assert!(matches!(solve_auto(&mut a, &[eq]), CheckResult::Sat(_)));
}

#[test]
fn bv2nat_out_of_range_target_is_unsat_or_unknown() {
    // bv2nat(x) == 300 with x : BitVec(8): impossible (max 255). The bounded
    // integer path reports unsat-in-range as unknown, never a wrong sat.
    let mut a = TermArena::new();
    let x = a.bv_var("x", 8).unwrap();
    let n = a.bv2nat(x).unwrap();
    let target = a.int_const(300);
    let eq = a.eq(n, target).unwrap();
    let r = solve_auto(&mut a, &[eq]);
    assert!(matches!(r, CheckResult::Unsat | CheckResult::Unknown(_)), "got {r:?}");
}

#[test]
fn int2bv_round_trip_is_sat() {
    // y : Int, int2bv(8, y) == 0x2a, bv2nat(int2bv(8, y)) == 42 -> sat (y = 42).
    let mut a = TermArena::new();
    let y = a.declare("y", Sort::Int).map(|s| a.var(s)).unwrap();
    let b = a.int2bv(8, y).unwrap();
    let lit = a.bv_const(8, 42).unwrap();
    let eq_bv = a.eq(b, lit).unwrap();
    let back = a.bv2nat(b).unwrap();
    let forty_two = a.int_const(42);
    let eq_int = a.eq(back, forty_two).unwrap();
    assert!(matches!(solve_auto(&mut a, &[eq_bv, eq_int]), CheckResult::Sat(_)));
}

#[test]
fn int2bv_wraps_modulo() {
    // int2bv(8, y) == 0 with y == 256 -> sat (256 mod 256 == 0).
    let mut a = TermArena::new();
    let y = a.declare("y", Sort::Int).map(|s| a.var(s)).unwrap();
    let c256 = a.int_const(256);
    let ye = a.eq(y, c256).unwrap();
    let b = a.int2bv(8, y).unwrap();
    let zero = a.bv_const(8, 0).unwrap();
    let eq = a.eq(b, zero).unwrap();
    assert!(matches!(solve_auto(&mut a, &[ye, eq]), CheckResult::Sat(_)));
}

#[test]
fn to_real_same_value_contradiction_is_unsat() {
    // to_real(i) > 5 AND to_real(i) < 5 : the same coerced value can't be both
    // (shared per-term relaxation catches it) -> unsat.
    let mut a = TermArena::new();
    let i = a.declare("i", Sort::Int).map(|s| a.var(s)).unwrap();
    let r = a.int_to_real(i).unwrap();
    let five = a.real_const(axeyum_ir::Rational::integer(5));
    let r2 = a.int_to_real(i).unwrap();
    let gt = a.real_gt(r, five).unwrap();
    let lt = a.real_lt(r2, five).unwrap();
    assert!(matches!(solve_auto(&mut a, &[gt, lt]), CheckResult::Unsat));
}

#[test]
fn to_real_pinned_is_sat() {
    // i == 3 AND to_real(i) == 3.0 : sat (replay confirms to_real(3) = 3.0).
    let mut a = TermArena::new();
    let i = a.declare("i", Sort::Int).map(|s| a.var(s)).unwrap();
    let three_i = a.int_const(3);
    let ic = a.eq(i, three_i).unwrap();
    let r = a.int_to_real(i).unwrap();
    let three_r = a.real_const(axeyum_ir::Rational::integer(3));
    let rc = a.eq(r, three_r).unwrap();
    assert!(matches!(solve_auto(&mut a, &[ic, rc]), CheckResult::Sat(_)));
}

#[test]
fn to_int_pinned_is_sat_and_contradiction_unsat() {
    // r == 7/2 AND to_int(r) == 3 : sat (floor(3.5) = 3).
    let mut a = TermArena::new();
    let r = a.declare("r", Sort::Real).map(|s| a.var(s)).unwrap();
    let half7 = a.real_const(axeyum_ir::Rational::new(7, 2));
    let rc = a.eq(r, half7).unwrap();
    let j = a.real_to_int(r).unwrap();
    let three = a.int_const(3);
    let jc = a.eq(j, three).unwrap();
    assert!(matches!(solve_auto(&mut a, &[rc, jc]), CheckResult::Sat(_)));

    // to_int(r) == 3 AND to_int(r) == 4 : same coerced value can't be both -> unsat.
    let mut a = TermArena::new();
    let r = a.declare("r", Sort::Real).map(|s| a.var(s)).unwrap();
    let j1 = a.real_to_int(r).unwrap();
    let j2 = a.real_to_int(r).unwrap();
    let three = a.int_const(3);
    let four = a.int_const(4);
    let c1 = a.eq(j1, three).unwrap();
    let c2 = a.eq(j2, four).unwrap();
    assert!(matches!(solve_auto(&mut a, &[c1, c2]), CheckResult::Unsat));
}

#[test]
fn is_int_pinned_is_sat() {
    // r == 4.0 AND is_int(r) : sat. r == 3.5 AND is_int(r) : replay fails -> not sat.
    let mut a = TermArena::new();
    let r = a.declare("r", Sort::Real).map(|s| a.var(s)).unwrap();
    let four = a.real_const(axeyum_ir::Rational::integer(4));
    let rc = a.eq(r, four).unwrap();
    let ii = a.real_is_int(r).unwrap();
    assert!(matches!(solve_auto(&mut a, &[rc, ii]), CheckResult::Sat(_)));

    // is_int(r) AND not(is_int(r)) : same value can't be both -> unsat.
    let mut a = TermArena::new();
    let r = a.declare("r", Sort::Real).map(|s| a.var(s)).unwrap();
    let i1 = a.real_is_int(r).unwrap();
    let i2 = a.real_is_int(r).unwrap();
    let n2 = a.not(i2).unwrap();
    assert!(matches!(solve_auto(&mut a, &[i1, n2]), CheckResult::Unsat));
}
