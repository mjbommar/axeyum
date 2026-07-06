//! Proof-method scenarios: direct, contrapositive, contradiction, and case
//! analysis as refutation.
//!
//! Exercises the
//! [proof-methods](../../../docs/curriculum/00-foundations/proof-methods.md)
//! node: each classical proof pattern *is* a refutation shape — to prove a
//! claim, assert its negation and derive UNSAT (negate-and-decide). The
//! theorem scenarios are UNSAT-of-negation over exhaustively enumerable
//! Boolean/bit-vector domains, and one deliberately false conjecture is SAT
//! with a concrete counterexample witness — the "disproof by counterexample"
//! pattern. Oracle-free per ADR-0008.

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, UnsatEvidence};

fn bool_var(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::Bool).unwrap();
    arena.var(sym)
}

/// Packages a Boolean `violation` term (the negation of a theorem) as an UNSAT
/// scenario proven exhaustively over `total_bits` bits of declared symbols.
fn unsat(
    arena: TermArena,
    label: String,
    width: u32,
    total_bits: u32,
    violation: TermId,
) -> Scenario {
    let mut builder = Query::builder(&arena);
    builder.assert(violation).unwrap();
    let query = builder.build();
    Scenario {
        name: label,
        family: Family::ProofMethods,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << total_bits,
            },
        },
    }
}

/// **Contrapositive**: `(p → q) ↔ (¬q → ¬p)` is a tautology, so proving the
/// contrapositive proves the implication. The negation of the equivalence is
/// unsatisfiable (4 cases).
///
/// # Panics
///
/// Panics on arena corruption.
pub fn contrapositive_equivalence() -> Scenario {
    let mut arena = TermArena::new();
    let p = bool_var(&mut arena, "p");
    let q = bool_var(&mut arena, "q");
    let direct = arena.implies(p, q).unwrap();
    let not_q = arena.not(q).unwrap();
    let not_p = arena.not(p).unwrap();
    let contrapositive = arena.implies(not_q, not_p).unwrap();
    let equivalent = arena.eq(direct, contrapositive).unwrap();
    let violation = arena.not(equivalent).unwrap();
    unsat(
        arena,
        "proof_methods/contrapositive_equivalence".to_string(),
        1,
        2,
        violation,
    )
}

/// **Case analysis** (disjunction elimination): `(p → r) ∧ (q → r) ∧ (p ∨ q)`
/// entails `r`. The negation is unsatisfiable (8 cases).
///
/// # Panics
///
/// Panics on arena corruption.
pub fn case_analysis_elimination() -> Scenario {
    let mut arena = TermArena::new();
    let p = bool_var(&mut arena, "p");
    let q = bool_var(&mut arena, "q");
    let r = bool_var(&mut arena, "r");
    let from_p = arena.implies(p, r).unwrap();
    let from_q = arena.implies(q, r).unwrap();
    let some_case = arena.or(p, q).unwrap();
    let both = arena.and(from_p, from_q).unwrap();
    let premises = arena.and(both, some_case).unwrap();
    let theorem = arena.implies(premises, r).unwrap();
    let violation = arena.not(theorem).unwrap();
    unsat(
        arena,
        "proof_methods/case_analysis_elimination".to_string(),
        1,
        3,
        violation,
    )
}

/// **Proof by contradiction**: to prove "`n` odd ⇒ `n²` odd", assume `n` odd
/// *and* `n²` even; the assumption set is unsatisfiable over any bit-vector
/// width (parity is the low bit, and the low bit of `n·n` is the square of the
/// low bit of `n`).
///
/// # Panics
///
/// Panics if `width` exceeds the budget or on arena corruption.
pub fn contradiction_odd_square(width: u32) -> Scenario {
    assert!(
        (1..=20).contains(&width),
        "contradiction_odd_square stays inside the budget"
    );
    let mut arena = TermArena::new();
    let n_sym = arena.declare("n", Sort::BitVec(width)).unwrap();
    let n = arena.var(n_sym);
    let one = arena.bv_const(width, 1).unwrap();
    let zero = arena.bv_const(width, 0).unwrap();
    let two = arena.bv_const(width, 2).unwrap();
    let n_parity = arena.bv_urem(n, two).unwrap();
    let n_odd = arena.eq(n_parity, one).unwrap();
    let square = arena.bv_mul(n, n).unwrap();
    let square_parity = arena.bv_urem(square, two).unwrap();
    let square_even = arena.eq(square_parity, zero).unwrap();
    let violation = arena.and(n_odd, square_even).unwrap();
    unsat(
        arena,
        format!("proof_methods/contradiction_odd_square_w{width}"),
        width,
        width,
        violation,
    )
}

/// **Disproof by counterexample**: the plausible conjecture "`x² ≥ x` for all
/// `x`" fails over fixed-width (wrapping) arithmetic. The scenario asserts
/// `x·x <ᵤ x` and is satisfiable, witnessed by `x = 2^(width−1) + 2` (whose
/// square wraps to `4`).
///
/// # Panics
///
/// Panics if `width` is outside `4..=20` or on arena corruption.
pub fn counterexample_square_growth(width: u32) -> Scenario {
    assert!(
        (4..=20).contains(&width),
        "counterexample_square_growth supports widths 4..=20"
    );
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    let square = arena.bv_mul(x, x).unwrap();
    let wrapped = arena.bv_ult(square, x).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(wrapped).unwrap();
    let query = builder.build();

    // x = 2^(width-1) + 2: x^2 = 2^(2w-2) + 2^w + 4 ≡ 4 (mod 2^w) for w >= 4,
    // and 4 < 2^(width-1) + 2.
    let witness_value = (1u128 << (width - 1)) + 2;
    let mut witness = Assignment::new();
    witness.set(
        x_sym,
        Value::Bv {
            width,
            value: witness_value,
        },
    );

    Scenario {
        name: format!("proof_methods/counterexample_square_growth_w{width}"),
        family: Family::ProofMethods,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// A deterministic catalog of proof-method scenarios.
pub fn proof_methods_catalog() -> Vec<Scenario> {
    vec![
        contrapositive_equivalence(),
        case_analysis_elimination(),
        contradiction_odd_square(6),
        contradiction_odd_square(10),
        counterexample_square_growth(4),
        counterexample_square_growth(8),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_methods_catalog_self_checks() {
        for scenario in proof_methods_catalog() {
            assert_eq!(scenario.family, Family::ProofMethods);
            scenario.self_check().unwrap_or_else(|e| {
                panic!(
                    "proof-methods scenario {} failed self-check: {e}",
                    scenario.name
                )
            });
        }
    }

    #[test]
    fn counterexample_witness_wraps() {
        // The disproof scenario must be satisfiable with the stated witness.
        let scenario = counterexample_square_growth(4);
        assert!(matches!(scenario.expectation, Expectation::Sat { .. }));
        scenario.self_check().unwrap();
    }
}
