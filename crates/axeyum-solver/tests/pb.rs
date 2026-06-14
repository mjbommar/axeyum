//! Weighted pseudo-Boolean constraints over Booleans.

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, pb_eq, pb_ge, pb_le, solve};

fn bool_var(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::Bool).unwrap();
    arena.var(sym)
}

#[test]
fn weighted_le_bounds_the_sum() {
    // 3a + 2b + 2c <= 4, and require b. Then a must be false (3+2 = 5 > 4), and
    // at most one more weight-2 fits: b alone (2) or b+? no — 2+2=4 ok, so b and c
    // can both hold (2+2=4). But a=true would force >=3, +2(b) = 5 > 4 -> a false.
    let mut arena = TermArena::new();
    let a = bool_var(&mut arena, "a");
    let b = bool_var(&mut arena, "b");
    let c = bool_var(&mut arena, "c");
    let le = pb_le(&mut arena, &[(a, 3), (b, 2), (c, 2)], 4).unwrap();
    // Force a and b true: 3 + 2 = 5 > 4 -> unsat.
    assert!(matches!(
        solve(&mut arena, &[le, a, b], &SolverConfig::default()),
        Ok(CheckResult::Unsat)
    ));
}

#[test]
fn weighted_ge_requires_enough_weight() {
    // 3a + 1b + 1c >= 3 with a forced false -> need b and c (1+1=2 < 3) -> unsat.
    let mut arena = TermArena::new();
    let a = bool_var(&mut arena, "a");
    let b = bool_var(&mut arena, "b");
    let c = bool_var(&mut arena, "c");
    let na = arena.not(a).unwrap();
    let ge = pb_ge(&mut arena, &[(a, 3), (b, 1), (c, 1)], 3).unwrap();
    assert!(matches!(
        solve(&mut arena, &[ge, na], &SolverConfig::default()),
        Ok(CheckResult::Unsat)
    ));
}

#[test]
fn weighted_ge_is_satisfiable_with_the_heavy_literal() {
    // 3a + 1b + 1c >= 3 is satisfiable with a = true.
    let mut arena = TermArena::new();
    let a = bool_var(&mut arena, "a");
    let b = bool_var(&mut arena, "b");
    let c = bool_var(&mut arena, "c");
    let ge = pb_ge(&mut arena, &[(a, 3), (b, 1), (c, 1)], 3).unwrap();
    assert!(matches!(
        solve(&mut arena, &[ge, a], &SolverConfig::default()),
        Ok(CheckResult::Sat(_))
    ));
}

#[test]
fn weighted_eq_pins_the_sum() {
    // 2a + 2b + 1c == 3  with a true -> 2 + (2b + 1c) == 3 -> need c, not b.
    let mut arena = TermArena::new();
    let a = bool_var(&mut arena, "a");
    let b = bool_var(&mut arena, "b");
    let c = bool_var(&mut arena, "c");
    let eq = pb_eq(&mut arena, &[(a, 2), (b, 2), (c, 1)], 3).unwrap();
    // a and b both true -> 2+2 = 4 != 3 (even before c) -> unsat.
    assert!(matches!(
        solve(&mut arena, &[eq, a, b], &SolverConfig::default()),
        Ok(CheckResult::Unsat)
    ));
}
