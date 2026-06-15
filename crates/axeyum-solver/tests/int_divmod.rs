//! Euclidean div/mod/abs decided completely (sat AND unsat) via the LIA
//! simplex/DPLL path, after elimination to linear constraints. The bounded
//! bit-blaster alone reports in-range unsat as unknown; these must be unsat.

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn int(arena: &mut TermArena, name: &str) -> axeyum_ir::TermId {
    let s = arena.declare(name, Sort::Int).unwrap();
    arena.var(s)
}

fn run(arena: &mut TermArena, asserts: &[axeyum_ir::TermId]) -> CheckResult {
    solve(arena, asserts, &SolverConfig::default()).expect("decides without error")
}

#[test]
fn contradictory_mod_is_unsat() {
    // mod(x,3) == 1 AND mod(x,3) == 2 : impossible -> genuine unsat.
    let mut a = TermArena::new();
    let x = int(&mut a, "x");
    let three = a.int_const(3);
    let m = a.int_mod(x, three).unwrap();
    let one = a.int_const(1);
    let two = a.int_const(2);
    let c1 = a.eq(m, one).unwrap();
    let m2 = a.int_mod(x, three).unwrap();
    let c2 = a.eq(m2, two).unwrap();
    assert!(
        matches!(run(&mut a, &[c1, c2]), CheckResult::Unsat),
        "contradictory mod"
    );
}

#[test]
fn mod_out_of_range_value_is_unsat() {
    // mod(x,3) == 3 is unsat (Euclidean mod is in 0..3); == -1 likewise.
    for bad in [3i128, -1] {
        let mut a = TermArena::new();
        let x = int(&mut a, "x");
        let three = a.int_const(3);
        let m = a.int_mod(x, three).unwrap();
        let b = a.int_const(bad);
        let eq = a.eq(m, b).unwrap();
        assert!(
            matches!(run(&mut a, &[eq]), CheckResult::Unsat),
            "mod==^{bad} unsat"
        );
    }
}

#[test]
fn inconsistent_div_is_unsat() {
    // div(x,2) == 3 AND x == 5 : div(5,2)=2 != 3 -> unsat.
    let mut a = TermArena::new();
    let x = int(&mut a, "x");
    let two = a.int_const(2);
    let d = a.int_div(x, two).unwrap();
    let three = a.int_const(3);
    let dc = a.eq(d, three).unwrap();
    let five = a.int_const(5);
    let xc = a.eq(x, five).unwrap();
    assert!(
        matches!(run(&mut a, &[dc, xc]), CheckResult::Unsat),
        "div(5,2)=2!=3"
    );
}

#[test]
fn abs_contradiction_is_unsat() {
    // abs(x) == 3 AND x == 5 -> unsat.
    let mut a = TermArena::new();
    let x = int(&mut a, "x");
    let av = a.int_abs(x).unwrap();
    let three = a.int_const(3);
    let ac = a.eq(av, three).unwrap();
    let five = a.int_const(5);
    let xc = a.eq(x, five).unwrap();
    assert!(
        matches!(run(&mut a, &[ac, xc]), CheckResult::Unsat),
        "abs(5)=5!=3"
    );
}

#[test]
fn abs_negative_is_unsat() {
    // abs(x) == -1 is unsat (abs is non-negative).
    let mut a = TermArena::new();
    let x = int(&mut a, "x");
    let av = a.int_abs(x).unwrap();
    let neg1 = a.int_const(-1);
    let eq = a.eq(av, neg1).unwrap();
    assert!(
        matches!(run(&mut a, &[eq]), CheckResult::Unsat),
        "abs == -1"
    );
}

#[test]
fn euclidean_mod_negative_is_sat_and_consistent() {
    // x == -7 AND mod(x,3) == 2 : sat (Euclidean -7 mod 3 = 2, not -1).
    let mut a = TermArena::new();
    let x = int(&mut a, "x");
    let neg7 = a.int_const(-7);
    let xc = a.eq(x, neg7).unwrap();
    let three = a.int_const(3);
    let m = a.int_mod(x, three).unwrap();
    let two = a.int_const(2);
    let mc = a.eq(m, two).unwrap();
    assert!(
        matches!(run(&mut a, &[xc, mc]), CheckResult::Sat(_)),
        "-7 mod 3 = 2"
    );
    // and mod == 1 would be wrong -> unsat
    let mut a = TermArena::new();
    let x = int(&mut a, "x");
    let neg7 = a.int_const(-7);
    let xc = a.eq(x, neg7).unwrap();
    let three = a.int_const(3);
    let m = a.int_mod(x, three).unwrap();
    let one = a.int_const(1);
    let mc = a.eq(m, one).unwrap();
    assert!(
        matches!(run(&mut a, &[xc, mc]), CheckResult::Unsat),
        "-7 mod 3 != 1"
    );
}

#[test]
fn satisfiable_divmod_still_sat() {
    // mod(x,3) == 2 AND 0 < x < 100 : sat (e.g. x = 2).
    let mut a = TermArena::new();
    let x = int(&mut a, "x");
    let three = a.int_const(3);
    let m = a.int_mod(x, three).unwrap();
    let two = a.int_const(2);
    let mc = a.eq(m, two).unwrap();
    let zero = a.int_const(0);
    let hundred = a.int_const(100);
    let lo = a.int_gt(x, zero).unwrap();
    let hi = a.int_lt(x, hundred).unwrap();
    assert!(matches!(run(&mut a, &[mc, lo, hi]), CheckResult::Sat(_)));
}
