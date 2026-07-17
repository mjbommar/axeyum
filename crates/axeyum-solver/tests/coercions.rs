//! Bit-vector / integer coercions (`bv2nat` / `int2bv`) through the auto
//! dispatcher's combined bit-blasting path (arrays/funcs/integers to `QF_BV`).
#![cfg(feature = "full")]

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
    assert!(
        matches!(r, CheckResult::Unsat | CheckResult::Unknown(_)),
        "got {r:?}"
    );
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
    assert!(matches!(
        solve_auto(&mut a, &[eq_bv, eq_int]),
        CheckResult::Sat(_)
    ));
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

#[test]
fn bounded_to_real_is_completely_decided() {
    // 0 <= i <= 3 AND to_real(i) > 5 : unsat. The bounded linking ties
    // to_real(i) exactly to i over {0,1,2,3}, so this is decided (not unknown).
    let mut a = TermArena::new();
    let i = a.declare("i", Sort::Int).map(|s| a.var(s)).unwrap();
    let zero = a.int_const(0);
    let three = a.int_const(3);
    let lo = a.int_ge(i, zero).unwrap();
    let hi = a.int_le(i, three).unwrap();
    let r = a.int_to_real(i).unwrap();
    let five = a.real_const(axeyum_ir::Rational::integer(5));
    let gt = a.real_gt(r, five).unwrap();
    assert!(
        matches!(solve_auto(&mut a, &[lo, hi, gt]), CheckResult::Unsat),
        "0<=i<=3 ∧ to_real(i)>5 must be unsat"
    );
}

#[test]
fn bounded_to_real_feasible_is_sat() {
    // 0 <= i <= 3 AND to_real(i) > 2.5 : sat (i = 3, to_real(i) = 3 > 2.5).
    let mut a = TermArena::new();
    let i = a.declare("i", Sort::Int).map(|s| a.var(s)).unwrap();
    let zero = a.int_const(0);
    let three = a.int_const(3);
    let lo = a.int_ge(i, zero).unwrap();
    let hi = a.int_le(i, three).unwrap();
    let r = a.int_to_real(i).unwrap();
    let two_half = a.real_const(axeyum_ir::Rational::new(5, 2));
    let gt = a.real_gt(r, two_half).unwrap();
    assert!(
        matches!(solve_auto(&mut a, &[lo, hi, gt]), CheckResult::Sat(_)),
        "0<=i<=3 ∧ to_real(i)>2.5 must be sat"
    );
}

#[test]
fn to_real_vs_constant_is_exactly_decided() {
    // to_real(i) > 5.5 AND i < 6 : unsat (i>5.5 means i>=6, contradicts i<6).
    // Exact: no bounds needed, no relaxation -- the comparison rewrites to i>=6.
    let mut a = TermArena::new();
    let i = a.declare("i", Sort::Int).map(|s| a.var(s)).unwrap();
    let r = a.int_to_real(i).unwrap();
    let c = a.real_const(axeyum_ir::Rational::new(11, 2)); // 5.5
    let gt = a.real_gt(r, c).unwrap();
    let six = a.int_const(6);
    let lt = a.int_lt(i, six).unwrap();
    assert!(
        matches!(solve_auto(&mut a, &[gt, lt]), CheckResult::Unsat),
        "to_real(i)>5.5 ∧ i<6 unsat"
    );

    // to_real(i) == 3.5 : unsat (no integer equals 3.5).
    let mut a = TermArena::new();
    let i = a.declare("i", Sort::Int).map(|s| a.var(s)).unwrap();
    let r = a.int_to_real(i).unwrap();
    let c = a.real_const(axeyum_ir::Rational::new(7, 2)); // 3.5
    let eq = a.eq(r, c).unwrap();
    assert!(
        matches!(solve_auto(&mut a, &[eq]), CheckResult::Unsat),
        "to_real(i)=3.5 unsat"
    );

    // to_real(i) <= 2.9 AND i >= 0 : sat (i ∈ {0,1,2}).
    let mut a = TermArena::new();
    let i = a.declare("i", Sort::Int).map(|s| a.var(s)).unwrap();
    let r = a.int_to_real(i).unwrap();
    let c = a.real_const(axeyum_ir::Rational::new(29, 10)); // 2.9
    let le = a.real_le(r, c).unwrap();
    let zero = a.int_const(0);
    let ge = a.int_ge(i, zero).unwrap();
    assert!(
        matches!(solve_auto(&mut a, &[le, ge]), CheckResult::Sat(_)),
        "to_real(i)<=2.9 ∧ i>=0 sat"
    );
}

#[test]
fn to_int_vs_constant_is_exactly_decided() {
    // to_int(r) == 3 AND r == 3.5 : sat (floor(3.5) = 3).
    let mut a = TermArena::new();
    let r = a.declare("r", Sort::Real).map(|s| a.var(s)).unwrap();
    let j = a.real_to_int(r).unwrap();
    let three = a.int_const(3);
    let je = a.eq(j, three).unwrap();
    let half7 = a.real_const(axeyum_ir::Rational::new(7, 2));
    let re = a.eq(r, half7).unwrap();
    assert!(
        matches!(solve_auto(&mut a, &[je, re]), CheckResult::Sat(_)),
        "to_int(3.5)=3 sat"
    );

    // to_int(r) >= 5 AND r < 5.0 : unsat (floor(r)>=5 needs r>=5).
    let mut a = TermArena::new();
    let r = a.declare("r", Sort::Real).map(|s| a.var(s)).unwrap();
    let j = a.real_to_int(r).unwrap();
    let five = a.int_const(5);
    let ge = a.int_ge(j, five).unwrap();
    let five_r = a.real_const(axeyum_ir::Rational::integer(5));
    let lt = a.real_lt(r, five_r).unwrap();
    assert!(
        matches!(solve_auto(&mut a, &[ge, lt]), CheckResult::Unsat),
        "to_int(r)>=5 ∧ r<5 unsat"
    );
}

#[test]
fn to_real_vs_to_real_is_exact() {
    // to_real(i) < to_real(j) AND i >= j : unsat (i<j ⟺ to_real(i)<to_real(j)).
    let mut a = TermArena::new();
    let i = a.declare("i", Sort::Int).map(|s| a.var(s)).unwrap();
    let j = a.declare("j", Sort::Int).map(|s| a.var(s)).unwrap();
    let ri = a.int_to_real(i).unwrap();
    let rj = a.int_to_real(j).unwrap();
    let lt = a.real_lt(ri, rj).unwrap();
    let ge = a.int_ge(i, j).unwrap();
    assert!(
        matches!(solve_auto(&mut a, &[lt, ge]), CheckResult::Unsat),
        "to_real(i)<to_real(j) ∧ i>=j unsat"
    );
}

#[test]
fn sum_of_to_real_vs_constant_is_exact() {
    // to_real(x) + to_real(y) <= 5.5 AND x + y >= 6 : unsat. The sum of coercions
    // folds to to_real(x+y), then <= 5.5 rewrites to (x+y) <= 5.
    let mut a = TermArena::new();
    let x = a.declare("x", Sort::Int).map(|s| a.var(s)).unwrap();
    let y = a.declare("y", Sort::Int).map(|s| a.var(s)).unwrap();
    let rx = a.int_to_real(x).unwrap();
    let ry = a.int_to_real(y).unwrap();
    let sum = a.real_add(rx, ry).unwrap();
    let c = a.real_const(axeyum_ir::Rational::new(11, 2)); // 5.5
    let le = a.real_le(sum, c).unwrap();
    let isum = a.int_add(x, y).unwrap();
    let six = a.int_const(6);
    let ge = a.int_ge(isum, six).unwrap();
    assert!(
        matches!(solve_auto(&mut a, &[le, ge]), CheckResult::Unsat),
        "to_real(x)+to_real(y)<=5.5 ∧ x+y>=6 unsat"
    );
}

// --- Mixed integer/real (QF_LIRA) by branch-and-bound (ADR-pending MILP) ------
// These couple an integer to a *real variable* via `to_real`, so the exact
// "coerced int vs constant" rewrites don't apply; only the mixed-integer
// branch-and-bound decides them (the bounded coercion relaxation returns
// `unknown`).

#[test]
fn milp_coerced_integer_vs_real_var_unsat() {
    // to_real(x) == y && 1000.3 < y < 1000.9: no integer x has a real image in
    // that open interval, so unsat. Branch-and-bound: x<=1000 and x>=1001 both
    // contradict the bounds (each leaf's LP is Farkas-refuted).
    use axeyum_ir::Rational;
    let mut a = TermArena::new();
    let x = a.int_var("x").unwrap();
    let y = a.real_var("y").unwrap();
    let xr = a.int_to_real(x).unwrap();
    let eq = a.eq(xr, y).unwrap();
    let lo = a.real_const(Rational::new(10003, 10)); // 1000.3
    let hi = a.real_const(Rational::new(10009, 10)); // 1000.9
    let gt = a.real_gt(y, lo).unwrap();
    let lt = a.real_lt(y, hi).unwrap();
    assert!(matches!(
        solve_auto(&mut a, &[eq, gt, lt]),
        CheckResult::Unsat
    ));
}

#[test]
fn milp_coerced_integer_vs_real_var_sat() {
    // to_real(x) == y && 1000.3 < y < 1001.3: x = 1001 (image 1001.0) works.
    // Decided sat and replayed against the original (to_real coupling holds).
    use axeyum_ir::Rational;
    let mut a = TermArena::new();
    let x = a.int_var("x").unwrap();
    let y = a.real_var("y").unwrap();
    let xr = a.int_to_real(x).unwrap();
    let eq = a.eq(xr, y).unwrap();
    let lo = a.real_const(Rational::new(10003, 10)); // 1000.3
    let hi = a.real_const(Rational::new(10013, 10)); // 1001.3
    let gt = a.real_gt(y, lo).unwrap();
    let lt = a.real_lt(y, hi).unwrap();
    assert!(matches!(
        solve_auto(&mut a, &[eq, gt, lt]),
        CheckResult::Sat(_)
    ));
}
