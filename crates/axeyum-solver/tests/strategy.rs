//! Swappable solving strategies (ADR-0019): the same query decided through the
//! unified `solve_with_strategy` entry point, and — when the `z3` feature is on
//! — cross-validation that the high-memory eager pure-Rust strategy and the
//! low-memory Z3 oracle strategy agree on every verdict.

use axeyum_ir::{TermArena, TermId};
use axeyum_solver::{
    CheckResult, SolverConfig, Strategy, solve_lazy_bv_abstraction, solve_with_strategy,
};

/// The pure-Rust strategies, always available (no `z3` feature needed).
const PURE_RUST: &[Strategy] = &[
    Strategy::EagerPureRust,
    Strategy::LazyBvAbstraction,
    Strategy::Auto,
];

fn is_sat(result: &CheckResult) -> Option<bool> {
    match result {
        CheckResult::Sat(_) => Some(true),
        CheckResult::Unsat => Some(false),
        CheckResult::Unknown(_) => None,
    }
}

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
    assert_eq!(Strategy::LazyBvAbstraction.name(), "lazy-bv-abstraction");
    assert_eq!(Strategy::Auto.name(), "auto");
    assert!(Strategy::EagerPureRust.is_pure_rust());
    assert!(Strategy::LazyBvAbstraction.is_pure_rust());
    assert!(Strategy::Auto.is_pure_rust());
}

#[test]
fn pure_rust_strategies_decide_the_battery() {
    let config = SolverConfig::default();
    for &strategy in PURE_RUST {
        let mut arena = TermArena::new();
        let cases = battery(&mut arena);
        for (name, terms, expect_sat) in &cases {
            let result = solve_with_strategy(&mut arena, terms, &config, strategy)
                .unwrap_or_else(|error| panic!("{name}/{}: errored: {error}", strategy.name()));
            match (result, expect_sat) {
                (CheckResult::Sat(_), true) | (CheckResult::Unsat, false) => {}
                (other, _) => {
                    panic!(
                        "{name}/{}: expected sat={expect_sat}, got {other:?}",
                        strategy.name()
                    )
                }
            }
        }
    }
}

#[test]
fn eager_and_lazy_strategies_agree() {
    let config = SolverConfig::default();
    let mut arena = TermArena::new();
    let cases = battery(&mut arena);
    for (name, terms, _expect) in &cases {
        let eager =
            solve_with_strategy(&mut arena, terms, &config, Strategy::EagerPureRust).unwrap();
        let lazy =
            solve_with_strategy(&mut arena, terms, &config, Strategy::LazyBvAbstraction).unwrap();
        if let (Some(a), Some(b)) = (is_sat(&eager), is_sat(&lazy)) {
            assert_eq!(a, b, "{name}: eager/lazy disagree");
        }
    }
}

/// The lazy strategy decides `x*y == 6 AND x*y == 7` UNSAT **without bit-blasting
/// the multiplier at all** — the abstraction (`m == 6 AND m == 7`) is already
/// contradictory. This is the memory win the strategy exists for.
#[test]
fn lazy_strategy_refutes_without_materializing_the_multiplier() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 16).unwrap();
    let y = arena.bv_var("y", 16).unwrap();
    let xy = arena.bv_mul(x, y).unwrap();
    let six = arena.bv_const(16, 6).unwrap();
    let seven = arena.bv_const(16, 7).unwrap();
    let c1 = arena.eq(xy, six).unwrap();
    let c2 = arena.eq(xy, seven).unwrap();

    let outcome =
        solve_lazy_bv_abstraction(&mut arena, &[c1, c2], &SolverConfig::default()).unwrap();
    assert!(
        matches!(outcome.result, CheckResult::Unsat),
        "should be unsat"
    );
    assert_eq!(outcome.ops_total, 1, "one shared multiplier");
    assert_eq!(
        outcome.ops_refined, 0,
        "multiplier must never be bit-blasted for this refutation"
    );
}

/// The same memory win for division: `x udiv y == 6 AND x udiv y == 7` is
/// refuted without ever materializing the (heavy) restoring divider.
#[test]
fn lazy_strategy_refutes_division_without_materializing_it() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 16).unwrap();
    let y = arena.bv_var("y", 16).unwrap();
    let q = arena.bv_udiv(x, y).unwrap();
    let six = arena.bv_const(16, 6).unwrap();
    let seven = arena.bv_const(16, 7).unwrap();
    let c1 = arena.eq(q, six).unwrap();
    let c2 = arena.eq(q, seven).unwrap();

    let outcome =
        solve_lazy_bv_abstraction(&mut arena, &[c1, c2], &SolverConfig::default()).unwrap();
    assert!(matches!(outcome.result, CheckResult::Unsat));
    assert_eq!(outcome.ops_total, 1, "one shared divider");
    assert_eq!(outcome.ops_refined, 0, "divider never bit-blasted");
}

/// When the exact product *does* matter, the lazy strategy refines the
/// multiplier and still returns a genuine (replayed) model.
#[test]
fn lazy_strategy_refines_when_the_product_matters() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let xy = arena.bv_mul(x, y).unwrap();
    let six = arena.bv_const(8, 6).unwrap();
    let eq = arena.eq(xy, six).unwrap();

    let outcome = solve_lazy_bv_abstraction(&mut arena, &[eq], &SolverConfig::default()).unwrap();
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "x*y==6 is sat"
    );
    assert_eq!(outcome.ops_refined, 1, "the product matters, so refine it");
}

#[cfg(feature = "z3")]
#[test]
fn eager_and_oracle_strategies_agree() {
    let mut arena = TermArena::new();
    let cases = battery(&mut arena);
    let config = SolverConfig::default();
    for (name, terms, _expect) in &cases {
        let eager =
            solve_with_strategy(&mut arena, terms, &config, Strategy::EagerPureRust).unwrap();
        let oracle = solve_with_strategy(&mut arena, terms, &config, Strategy::Oracle).unwrap();
        // An `unknown` from either side is not a disagreement.
        if let (Some(a), Some(b)) = (is_sat(&eager), is_sat(&oracle)) {
            assert_eq!(a, b, "{name}: eager/oracle disagree");
        }
    }
    assert_eq!(Strategy::Oracle.name(), "oracle-z3");
    assert!(!Strategy::Oracle.is_pure_rust());
}

/// `Strategy::Auto` on a *structural* (no heavy-op) query routes through the
/// word-level preprocessing path (ADR-0037): a top-level variable definition is
/// eliminated by `solve_eqs`, and the returned model still reconstructs the
/// eliminated variable and satisfies the original assertions. (No `bvmul`/div, so
/// Auto takes the structural→preprocess branch, not the lazy branch.)
#[test]
fn auto_strategy_preprocesses_structural_queries_soundly() {
    use axeyum_ir::{Sort, Value, eval};

    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y = arena.declare("y", Sort::BitVec(8)).unwrap();
    let (xv, yv) = (arena.var(x), arena.var(y));
    let one = arena.bv_const(8, 1).unwrap();
    let y1 = arena.bv_add(yv, one).unwrap();
    let x_def = arena.eq(xv, y1).unwrap(); // x = y + 1  (eliminable)
    let ten = arena.bv_const(8, 10).unwrap();
    let x_is_10 = arena.eq(xv, ten).unwrap(); // ⇒ y = 9
    let originals = [x_def, x_is_10];

    let config = SolverConfig::default();
    let result = solve_with_strategy(&mut arena, &originals, &config, Strategy::Auto).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("x = y+1 ∧ x = 10 is sat");
    };
    let assignment = model.to_assignment();
    for &a in &originals {
        assert_eq!(
            eval(&arena, a, &assignment).unwrap(),
            Value::Bool(true),
            "Auto's reconstructed model must satisfy the original assertion"
        );
    }
    assert_eq!(
        assignment.get(x),
        Some(Value::Bv {
            width: 8,
            value: 10
        })
    );
    assert_eq!(assignment.get(y), Some(Value::Bv { width: 8, value: 9 }));
}
