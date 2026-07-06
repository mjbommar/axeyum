//! Induction scenarios: base and step obligations as decidable instances.
//!
//! Exercises the
//! [induction](../../../docs/curriculum/00-foundations/induction.md) node: the
//! induction *schema* is undecidable, but each concrete base/step obligation is
//! a quantifier-free fact over a fixed width. A step obligation abstracts the
//! inductive hypothesis into a fresh symbol `s` (e.g. "`s` is the sum so far"),
//! so refuting `hypothesis ∧ ¬conclusion` proves the step for every value the
//! hypothesis admits — a ring identity that holds even under wraparound. A
//! deliberately false invariant's step is SAT with a concrete counterexample
//! witness. Oracle-free per ADR-0008.

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, UnsatEvidence};

fn bv_var(arena: &mut TermArena, name: &str, width: u32) -> TermId {
    let sym = arena.declare(name, Sort::BitVec(width)).unwrap();
    arena.var(sym)
}

/// Packages a Boolean `violation` term (some induction obligation fails) as an
/// UNSAT scenario proven exhaustively over `symbol_count` `width`-bit symbols.
fn unsat(
    arena: TermArena,
    label: String,
    width: u32,
    symbol_count: u32,
    violation: TermId,
) -> Scenario {
    let mut builder = Query::builder(&arena);
    builder.assert(violation).unwrap();
    let query = builder.build();
    Scenario {
        name: label,
        family: Family::Induction,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << (symbol_count * width),
            },
        },
    }
}

/// **Sum of the first `n` odd numbers is `n²`** — both obligations at once.
/// The scenario asserts "the base case fails, or the step fails":
/// `¬(0 = 0·0) ∨ (s = n·n ∧ s + 2n + 1 ≠ (n+1)·(n+1))`, which is
/// unsatisfiable: the base is arithmetic, and the step is the ring identity
/// `n² + 2n + 1 = (n+1)²` (true even with wraparound).
///
/// # Panics
///
/// Panics if `2 * width` exceeds the budget or on arena corruption.
pub fn sum_of_odds_obligations(width: u32) -> Scenario {
    assert!(
        2 * width <= 20,
        "sum_of_odds_obligations stays inside the budget"
    );
    let mut arena = TermArena::new();
    let n = bv_var(&mut arena, "n", width);
    let s = bv_var(&mut arena, "s", width);
    let zero = arena.bv_const(width, 0).unwrap();
    let one = arena.bv_const(width, 1).unwrap();

    // Base: 0 = 0·0.
    let zero_sq = arena.bv_mul(zero, zero).unwrap();
    let base = arena.eq(zero, zero_sq).unwrap();
    let base_fails = arena.not(base).unwrap();

    // Step: (s = n·n) ⇒ (s + 2n + 1 = (n+1)·(n+1)).
    let n_sq = arena.bv_mul(n, n).unwrap();
    let hypothesis = arena.eq(s, n_sq).unwrap();
    let two_n = arena.bv_add(n, n).unwrap();
    let s_plus = arena.bv_add(s, two_n).unwrap();
    let next_sum = arena.bv_add(s_plus, one).unwrap();
    let n_next = arena.bv_add(n, one).unwrap();
    let next_sq = arena.bv_mul(n_next, n_next).unwrap();
    let conclusion = arena.eq(next_sum, next_sq).unwrap();
    let not_conclusion = arena.not(conclusion).unwrap();
    let step_fails = arena.and(hypothesis, not_conclusion).unwrap();

    let violation = arena.or(base_fails, step_fails).unwrap();
    unsat(
        arena,
        format!("induction/sum_of_odds_obligations_w{width}"),
        width,
        2,
        violation,
    )
}

/// **Gauss sum** step obligation: from `2s = n(n+1)` conclude
/// `2(s + n + 1) = (n+1)(n+2)`. Asserting the hypothesis with the negated
/// conclusion is unsatisfiable — the ring identity `n(n+1) + 2(n+1) =
/// (n+1)(n+2)` holds at every width.
///
/// # Panics
///
/// Panics if `2 * width` exceeds the budget or on arena corruption.
pub fn gauss_sum_step(width: u32) -> Scenario {
    assert!(2 * width <= 20, "gauss_sum_step stays inside the budget");
    let mut arena = TermArena::new();
    let n = bv_var(&mut arena, "n", width);
    let s = bv_var(&mut arena, "s", width);
    let one = arena.bv_const(width, 1).unwrap();
    let two = arena.bv_const(width, 2).unwrap();

    let n_next = arena.bv_add(n, one).unwrap();
    let n_next2 = arena.bv_add(n_next, one).unwrap();

    // Hypothesis: 2s = n(n+1).
    let two_s = arena.bv_mul(two, s).unwrap();
    let n_prod = arena.bv_mul(n, n_next).unwrap();
    let hypothesis = arena.eq(two_s, n_prod).unwrap();

    // Conclusion: 2(s + n + 1) = (n+1)(n+2).
    let s_next_a = arena.bv_add(s, n).unwrap();
    let s_next = arena.bv_add(s_next_a, one).unwrap();
    let two_s_next = arena.bv_mul(two, s_next).unwrap();
    let next_prod = arena.bv_mul(n_next, n_next2).unwrap();
    let conclusion = arena.eq(two_s_next, next_prod).unwrap();

    let not_conclusion = arena.not(conclusion).unwrap();
    let violation = arena.and(hypothesis, not_conclusion).unwrap();
    unsat(
        arena,
        format!("induction/gauss_sum_step_w{width}"),
        width,
        2,
        violation,
    )
}

/// **A false invariant's step fails**: the claimed invariant "sum of the first
/// `n` odd numbers is `n² + n`" does not survive the step. The scenario asserts
/// `s = n² + n ∧ s + 2n + 1 ≠ (n+1)² + (n+1)` and is satisfiable, witnessed by
/// `n = 0, s = 0` (the step would need `1 = 2`).
///
/// # Panics
///
/// Panics if `width` is outside `2..=10` or on arena corruption.
pub fn bad_invariant_step(width: u32) -> Scenario {
    assert!(
        (2..=10).contains(&width),
        "bad_invariant_step supports widths 2..=10"
    );
    let mut arena = TermArena::new();
    let n_sym = arena.declare("n", Sort::BitVec(width)).unwrap();
    let s_sym = arena.declare("s", Sort::BitVec(width)).unwrap();
    let n = arena.var(n_sym);
    let s = arena.var(s_sym);
    let one = arena.bv_const(width, 1).unwrap();

    // Claimed invariant: s = n² + n.
    let n_sq = arena.bv_mul(n, n).unwrap();
    let claimed = arena.bv_add(n_sq, n).unwrap();
    let hypothesis = arena.eq(s, claimed).unwrap();

    // Step conclusion under the claim: s + 2n + 1 = (n+1)² + (n+1).
    let two_n = arena.bv_add(n, n).unwrap();
    let s_plus = arena.bv_add(s, two_n).unwrap();
    let next_sum = arena.bv_add(s_plus, one).unwrap();
    let n_next = arena.bv_add(n, one).unwrap();
    let next_sq = arena.bv_mul(n_next, n_next).unwrap();
    let next_claimed = arena.bv_add(next_sq, n_next).unwrap();
    let conclusion = arena.eq(next_sum, next_claimed).unwrap();
    let not_conclusion = arena.not(conclusion).unwrap();
    let violation = arena.and(hypothesis, not_conclusion).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(violation).unwrap();
    let query = builder.build();

    let mut witness = Assignment::new();
    witness.set(n_sym, Value::Bv { width, value: 0 });
    witness.set(s_sym, Value::Bv { width, value: 0 });

    Scenario {
        name: format!("induction/bad_invariant_step_w{width}"),
        family: Family::Induction,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// A deterministic catalog of induction scenarios.
pub fn induction_catalog() -> Vec<Scenario> {
    vec![
        sum_of_odds_obligations(6),
        sum_of_odds_obligations(8),
        gauss_sum_step(6),
        gauss_sum_step(8),
        bad_invariant_step(6),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn induction_catalog_self_checks() {
        for scenario in induction_catalog() {
            assert_eq!(scenario.family, Family::Induction);
            scenario.self_check().unwrap_or_else(|e| {
                panic!(
                    "induction scenario {} failed self-check: {e}",
                    scenario.name
                )
            });
        }
    }

    #[test]
    fn bad_invariant_witness_is_a_counterexample() {
        let scenario = bad_invariant_step(6);
        assert!(matches!(scenario.expectation, Expectation::Sat { .. }));
        scenario.self_check().unwrap();
    }
}
