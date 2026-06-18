//! Propositional-logic scenarios: the curriculum's bottom rung.
//!
//! Each scenario is either the negation of a propositional **tautology** (hence
//! unsatisfiable) or a satisfiable formula carrying a concrete witness. Both are
//! self-checked with no solver: UNSAT by an exhaustive truth table over the
//! Boolean variables (always within [`crate::EXHAUSTIVE_BIT_LIMIT`] here), SAT by
//! evaluating the witness. This closes the [`crate::Concept::PropositionalLogic`]
//! curriculum gap while giving the Boolean fragment self-checking test coverage.

use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, Value};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, UnsatEvidence};

/// Declares a fresh Boolean variable, returning its symbol and term.
fn boolean(arena: &mut TermArena, name: &str) -> (SymbolId, TermId) {
    let symbol = arena.declare(name, Sort::Bool).unwrap();
    (symbol, arena.var(symbol))
}

/// Packages a single asserted Boolean term as an UNSAT scenario proven by an
/// exhaustive truth table over `var_count` Boolean variables.
fn unsat(arena: TermArena, label: &'static str, var_count: u32, claim: TermId) -> Scenario {
    let mut builder = Query::builder(&arena);
    builder.assert(claim).unwrap();
    let query = builder.build();
    Scenario {
        name: format!("logic/{label}"),
        family: Family::Logic,
        width: 1,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << var_count,
            },
        },
    }
}

/// Negation of modus ponens `((p → q) ∧ p) → q` — unsatisfiable.
///
/// # Panics
///
/// Panics on arena corruption (never under normal construction).
pub fn modus_ponens() -> Scenario {
    let mut arena = TermArena::new();
    let (_p, p) = boolean(&mut arena, "p");
    let (_q, q) = boolean(&mut arena, "q");
    let p_implies_q = arena.implies(p, q).unwrap();
    let antecedent = arena.and(p_implies_q, p).unwrap();
    let tautology = arena.implies(antecedent, q).unwrap();
    let negation = arena.not(tautology).unwrap();
    unsat(arena, "modus_ponens", 2, negation)
}

/// Negation of the law of excluded middle `p ∨ ¬p` — unsatisfiable.
///
/// # Panics
///
/// Panics on arena corruption (never under normal construction).
pub fn excluded_middle() -> Scenario {
    let mut arena = TermArena::new();
    let (_p, p) = boolean(&mut arena, "p");
    let not_p = arena.not(p).unwrap();
    let tautology = arena.or(p, not_p).unwrap();
    let negation = arena.not(tautology).unwrap();
    unsat(arena, "excluded_middle", 1, negation)
}

/// The direct contradiction `p ∧ ¬p` — unsatisfiable.
///
/// # Panics
///
/// Panics on arena corruption (never under normal construction).
pub fn contradiction() -> Scenario {
    let mut arena = TermArena::new();
    let (_p, p) = boolean(&mut arena, "p");
    let not_p = arena.not(p).unwrap();
    let claim = arena.and(p, not_p).unwrap();
    unsat(arena, "contradiction", 1, claim)
}

/// Negation of the Boolean De Morgan law `¬(p ∧ q) ↔ (¬p ∨ ¬q)` —
/// unsatisfiable.
///
/// # Panics
///
/// Panics on arena corruption (never under normal construction).
pub fn de_morgan_law() -> Scenario {
    let mut arena = TermArena::new();
    let (_p, p) = boolean(&mut arena, "p");
    let (_q, q) = boolean(&mut arena, "q");
    let and = arena.and(p, q).unwrap();
    let lhs = arena.not(and).unwrap();
    let not_p = arena.not(p).unwrap();
    let not_q = arena.not(q).unwrap();
    let rhs = arena.or(not_p, not_q).unwrap();
    let iff = arena.eq(lhs, rhs).unwrap();
    let negation = arena.not(iff).unwrap();
    unsat(arena, "de_morgan", 2, negation)
}

/// A satisfiable formula `(p ∨ q) ∧ (¬p ∨ q)`, witnessed by `p = ⊥, q = ⊤`.
///
/// # Panics
///
/// Panics on arena corruption (never under normal construction).
pub fn satisfiable_clause() -> Scenario {
    let mut arena = TermArena::new();
    let (p_sym, p) = boolean(&mut arena, "p");
    let (q_sym, q) = boolean(&mut arena, "q");
    let clause1 = arena.or(p, q).unwrap();
    let not_p = arena.not(p).unwrap();
    let clause2 = arena.or(not_p, q).unwrap();
    let formula = arena.and(clause1, clause2).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(formula).unwrap();
    let query = builder.build();

    let mut witness = Assignment::new();
    witness.set(p_sym, Value::Bool(false));
    witness.set(q_sym, Value::Bool(true));

    Scenario {
        name: "logic/satisfiable_clause".to_string(),
        family: Family::Logic,
        width: 1,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// A deterministic catalog of propositional-logic scenarios.
pub fn logic_catalog() -> Vec<Scenario> {
    vec![
        modus_ponens(),
        excluded_middle(),
        contradiction(),
        de_morgan_law(),
        satisfiable_clause(),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn logic_catalog_self_checks() {
        let scenarios = logic_catalog();
        assert_eq!(scenarios.len(), 5);
        for scenario in scenarios {
            assert_eq!(scenario.family, Family::Logic);
            scenario.self_check().unwrap_or_else(|e| {
                panic!("logic scenario {} failed self-check: {e}", scenario.name)
            });
        }
    }

    #[test]
    fn tautology_negations_are_exhaustively_unsat() {
        // Each is proven over the full truth table, not sampled.
        for scenario in [
            modus_ponens(),
            excluded_middle(),
            de_morgan_law(),
            contradiction(),
        ] {
            match scenario.self_check().unwrap() {
                UnsatEvidence::Exhaustive { .. } => {}
                sampled @ UnsatEvidence::Sampled { .. } => {
                    panic!(
                        "{} expected exhaustive UNSAT, got {sampled:?}",
                        scenario.name
                    )
                }
            }
        }
    }
}
