//! The distinct (all-different) constraint.

use axeyum_ir::{TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, distinct, solve};

fn bv_var(arena: &mut TermArena, name: &str) -> TermId {
    arena.bv_var(name, 2).unwrap()
}

#[test]
fn three_distinct_over_two_bits_is_sat() {
    // Three BV2 values can be pairwise distinct (e.g. 0,1,2).
    let mut arena = TermArena::new();
    let xs = [
        bv_var(&mut arena, "a"),
        bv_var(&mut arena, "b"),
        bv_var(&mut arena, "c"),
    ];
    let all_diff = distinct(&mut arena, &xs).unwrap();
    assert!(matches!(
        solve(&mut arena, &[all_diff], &SolverConfig::default()),
        Ok(CheckResult::Sat(_))
    ));
}

#[test]
fn five_distinct_over_two_bits_is_unsat() {
    // Only 4 values exist in BV2, so 5 cannot be pairwise distinct (pigeonhole).
    let mut arena = TermArena::new();
    let xs = [
        bv_var(&mut arena, "a"),
        bv_var(&mut arena, "b"),
        bv_var(&mut arena, "c"),
        bv_var(&mut arena, "d"),
        bv_var(&mut arena, "e"),
    ];
    let all_diff = distinct(&mut arena, &xs).unwrap();
    assert!(matches!(
        solve(&mut arena, &[all_diff], &SolverConfig::default()),
        Ok(CheckResult::Unsat)
    ));
}

#[test]
fn singleton_distinct_is_trivially_true() {
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a");
    let d = distinct(&mut arena, &[a]).unwrap();
    assert!(matches!(
        solve(&mut arena, &[d], &SolverConfig::default()),
        Ok(CheckResult::Sat(_))
    ));
}
