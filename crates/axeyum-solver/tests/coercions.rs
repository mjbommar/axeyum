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
