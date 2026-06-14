//! Swappable solving strategies (ADR-0019): the same query decided through the
//! unified `solve_with_strategy` entry point, and — when the `z3` feature is on
//! — cross-validation that the high-memory eager pure-Rust strategy and the
//! low-memory Z3 oracle strategy agree on every verdict.

use axeyum_ir::{TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, Strategy, solve_with_strategy};

/// Builds a small battery of `QF_BV` queries with known verdicts: `(name,
/// terms, expect_sat)`.
fn battery(arena: &mut TermArena) -> Vec<(&'static str, Vec<TermId>, bool)> {
    let mut cases = Vec::new();

    // x + 1 == 5  over BV(8): sat (x = 4).
    {
        let x = arena.bv_var("x", 8).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let five = arena.bv_const(8, 5).unwrap();
        let xp1 = arena.bv_add(x, one).unwrap();
        let eq = arena.eq(xp1, five).unwrap();
        cases.push(("x+1==5", vec![eq], true));
    }
    // x == 3 and x == 7: unsat.
    {
        let x = arena.bv_var("x", 8).unwrap();
        let three = arena.bv_const(8, 3).unwrap();
        let seven = arena.bv_const(8, 7).unwrap();
        let a = arena.eq(x, three).unwrap();
        let b = arena.eq(x, seven).unwrap();
        cases.push(("x==3 & x==7", vec![a, b], false));
    }
    // x * y == 6 over BV(8): sat (2 * 3).
    {
        let x = arena.bv_var("mx", 8).unwrap();
        let y = arena.bv_var("my", 8).unwrap();
        let six = arena.bv_const(8, 6).unwrap();
        let xy = arena.bv_mul(x, y).unwrap();
        let eq = arena.eq(xy, six).unwrap();
        cases.push(("x*y==6", vec![eq], true));
    }
    // x != x: unsat.
    {
        let x = arena.bv_var("zx", 8).unwrap();
        let eqxx = arena.eq(x, x).unwrap();
        let ne = arena.not(eqxx).unwrap();
        cases.push(("x!=x", vec![ne], false));
    }

    cases
}

#[test]
fn strategy_metadata_is_stable() {
    assert_eq!(Strategy::default(), Strategy::EagerPureRust);
    assert_eq!(Strategy::EagerPureRust.name(), "eager-pure-rust");
    assert!(Strategy::EagerPureRust.is_pure_rust());
}

#[test]
fn eager_pure_rust_strategy_decides_the_battery() {
    let mut arena = TermArena::new();
    let cases = battery(&mut arena);
    let config = SolverConfig::default();
    for (name, terms, expect_sat) in &cases {
        let result = solve_with_strategy(&mut arena, terms, &config, Strategy::EagerPureRust)
            .unwrap_or_else(|error| panic!("{name}: eager strategy errored: {error}"));
        match (result, expect_sat) {
            (CheckResult::Sat(_), true) | (CheckResult::Unsat, false) => {}
            (other, _) => panic!("{name}: expected sat={expect_sat}, got {other:?}"),
        }
    }
}

#[cfg(feature = "z3")]
#[test]
fn eager_and_oracle_strategies_agree() {
    fn is_sat(result: &CheckResult) -> Option<bool> {
        match result {
            CheckResult::Sat(_) => Some(true),
            CheckResult::Unsat => Some(false),
            CheckResult::Unknown(_) => None,
        }
    }

    let mut arena = TermArena::new();
    let cases = battery(&mut arena);
    let config = SolverConfig::default();
    for (name, terms, _expect) in &cases {
        let eager =
            solve_with_strategy(&mut arena, terms, &config, Strategy::EagerPureRust).unwrap();
        let oracle = solve_with_strategy(&mut arena, terms, &config, Strategy::Oracle).unwrap();
        match (is_sat(&eager), is_sat(&oracle)) {
            (Some(a), Some(b)) => assert_eq!(a, b, "{name}: eager/oracle disagree"),
            // An `unknown` from either side is not a disagreement.
            _ => {}
        }
    }
    assert_eq!(Strategy::Oracle.name(), "oracle-z3");
    assert!(!Strategy::Oracle.is_pure_rust());
}
