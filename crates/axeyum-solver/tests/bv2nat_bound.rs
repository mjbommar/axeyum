//! `bv2nat` finite-range refutation (G2): `bv2nat(b)` of a `W`-bit vector lies in
//! `[0, 2^W - 1]`, so a constraint exceeding that range is `unsat` — and the
//! in-range satisfiable direction must keep deciding `sat`.

use axeyum_ir::TermArena;
use axeyum_solver::{CheckResult, SolverConfig, solve};

/// `bv2nat(4-bit) >= 16` exceeds the maximum 4-bit value (15): UNSAT.
#[test]
fn bv2nat_ge_2pow_is_unsat() {
    let mut a = TermArena::new();
    let b = a.bv_var("b", 4).unwrap();
    let n = a.bv2nat(b).unwrap();
    let sixteen = a.int_const(16);
    let ge = a.int_ge(n, sixteen).unwrap();
    assert!(matches!(
        solve(&mut a, &[ge], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

/// `bv2nat(4-bit) == 20` is unreachable (max is 15): UNSAT.
#[test]
fn bv2nat_eq_out_of_range_is_unsat() {
    let mut a = TermArena::new();
    let b = a.bv_var("b", 4).unwrap();
    let n = a.bv2nat(b).unwrap();
    let twenty = a.int_const(20);
    let eq = a.eq(n, twenty).unwrap();
    assert!(matches!(
        solve(&mut a, &[eq], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

/// `bv2nat(4-bit) >= 8` is satisfiable (e.g. `b = 8`): the working sat direction
/// must still decide — a regression guard for the additive fix.
#[test]
fn bv2nat_in_range_is_sat() {
    let mut a = TermArena::new();
    let b = a.bv_var("b", 4).unwrap();
    let n = a.bv2nat(b).unwrap();
    let eight = a.int_const(8);
    let ge = a.int_ge(n, eight).unwrap();
    assert!(matches!(
        solve(&mut a, &[ge], &SolverConfig::default()).unwrap(),
        CheckResult::Sat(_)
    ));
}

/// Two `bv2nat` of the **same** `b` (hash-consed to one term) constrained to two
/// distinct values: a single integer cannot be both 5 and 6, so UNSAT — this
/// checks the same `TermId` maps to one abstracted variable.
#[test]
fn bv2nat_same_b_two_values_is_unsat() {
    let mut a = TermArena::new();
    let b = a.bv_var("b", 4).unwrap();
    let n1 = a.bv2nat(b).unwrap();
    let n2 = a.bv2nat(b).unwrap();
    let five = a.int_const(5);
    let six = a.int_const(6);
    let e1 = a.eq(n1, five).unwrap();
    let e2 = a.eq(n2, six).unwrap();
    assert!(matches!(
        solve(&mut a, &[e1, e2], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

/// Two `bv2nat` of **distinct** vectors are independent: `bv2nat(b) == 5 ∧
/// bv2nat(c) == 6` is satisfiable — guards against collapsing distinct `b`/`c`
/// onto one abstracted variable.
#[test]
fn bv2nat_distinct_vectors_is_sat() {
    let mut a = TermArena::new();
    let b = a.bv_var("b", 4).unwrap();
    let c = a.bv_var("c", 4).unwrap();
    let nb = a.bv2nat(b).unwrap();
    let nc = a.bv2nat(c).unwrap();
    let five = a.int_const(5);
    let six = a.int_const(6);
    let eb = a.eq(nb, five).unwrap();
    let ec = a.eq(nc, six).unwrap();
    assert!(matches!(
        solve(&mut a, &[eb, ec], &SolverConfig::default()).unwrap(),
        CheckResult::Sat(_)
    ));
}

/// A wide width (32-bit): `bv2nat(b) >= 2^32` is UNSAT and must not OOM — the
/// width guard keeps `2^32 - 1` an exact `i128` constant. (Result must never be a
/// wrong `sat`; `unsat` or a graceful `unknown` are both acceptable.)
#[test]
fn bv2nat_wide_width_no_oom() {
    let mut a = TermArena::new();
    let b = a.bv_var("b", 32).unwrap();
    let n = a.bv2nat(b).unwrap();
    let big = a.int_const(1i128 << 32);
    let ge = a.int_ge(n, big).unwrap();
    assert!(matches!(
        solve(&mut a, &[ge], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat | CheckResult::Unknown(_)
    ));
}
