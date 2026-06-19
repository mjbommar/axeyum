//! Predicate-logic scenarios: quantifiers over a finite bit-vector domain.
//!
//! Over a finite domain a quantifier is a finite conjunction (`∀`) or
//! disjunction (`∃`), so closed first-order formulas are decidable by expansion
//! — exactly what the [predicate-logic](../../../docs/curriculum/00-foundations/predicate-logic.md)
//! node teaches and what axeyum's finite-domain quantifier evaluation does. The
//! scenarios are closed (no free symbols): a `∀`/`∃` theorem is UNSAT-of-negation
//! (the single empty assignment falsifies the negation), and a satisfiable
//! existential carries the (trivial) empty witness, the evaluator finding the
//! witnessing element internally. Oracle-free per ADR-0008.

use axeyum_ir::{Assignment, Sort, TermArena};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, UnsatEvidence};

/// `∀x. x + 0 = x` over `BitVec(width)` — a closed universal theorem; its
/// negation is unsatisfiable.
///
/// # Panics
///
/// Panics if `width` exceeds the budget or on arena corruption.
pub fn forall_additive_identity(width: u32) -> Scenario {
    assert!(
        width <= 16,
        "forall_additive_identity stays inside the budget"
    );
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.bv_const(width, 0).unwrap();
    let sum = arena.bv_add(x, zero).unwrap();
    let body = arena.eq(sum, x).unwrap();
    let claim = arena.forall(x_sym, body).unwrap();
    let negation = arena.not(claim).unwrap();
    closed_unsat(
        arena,
        format!("predicate/forall_additive_identity_w{width}"),
        width,
        negation,
    )
}

/// `∀x. ∃y. x + y = 0` over `BitVec(width)` — quantifier *alternation*: every
/// element has an additive inverse. A closed theorem; its negation is
/// unsatisfiable.
///
/// # Panics
///
/// Panics if `2 * width` exceeds the budget or on arena corruption.
pub fn forall_exists_inverse(width: u32) -> Scenario {
    assert!(
        2 * width <= 16,
        "forall_exists_inverse stays inside the budget"
    );
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let y_sym = arena.declare("y", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let zero = arena.bv_const(width, 0).unwrap();
    let sum = arena.bv_add(x, y).unwrap();
    let body = arena.eq(sum, zero).unwrap();
    let inner = arena.exists(y_sym, body).unwrap();
    let claim = arena.forall(x_sym, inner).unwrap();
    let negation = arena.not(claim).unwrap();
    closed_unsat(
        arena,
        format!("predicate/forall_exists_inverse_w{width}"),
        width,
        negation,
    )
}

/// `∃x. x · x = 4` over `BitVec(width)` — a satisfiable existential, witnessed
/// internally by `x = 2`. The scenario carries the trivial empty assignment; the
/// evaluator finds the witnessing element.
///
/// # Panics
///
/// Panics if `width` is outside `3..=16` or on arena corruption.
pub fn exists_square_root(width: u32) -> Scenario {
    assert!(
        (3..=16).contains(&width),
        "exists_square_root supports widths 3..=16"
    );
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    let square = arena.bv_mul(x, x).unwrap();
    let four = arena.bv_const(width, 4).unwrap();
    let body = arena.eq(square, four).unwrap();
    let claim = arena.exists(x_sym, body).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(claim).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("predicate/exists_square_root_w{width}"),
        family: Family::Predicate,
        width,
        seed: 0,
        // A closed satisfiable formula: the empty assignment suffices, the
        // evaluator enumerates the bound variable to find x = 2.
        expectation: Expectation::Sat {
            witness: Assignment::new(),
        },
        arena,
        query,
    }
}

/// **Fermat's little theorem** at a fixed prime `p`: `∀a. (0<a<p ⇒ a^(p−1) ≡ 1
/// (mod p))`. A closed universal theorem; its negation is unsatisfiable. Only
/// `p ∈ {3, 5}` is supported (the width must hold `a^(p−1)` without wraparound:
/// `p=3 ⇒ width 3`, `p=5 ⇒ width 9`).
///
/// # Panics
///
/// Panics if `p` is not 3 or 5, or on arena corruption.
pub fn fermat_little_theorem(p: u128) -> Scenario {
    let (exp, width) = match p {
        3 => (2u32, 3u32),
        5 => (4u32, 9u32),
        _ => panic!("fermat_little_theorem supports p in {{3, 5}}"),
    };
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(width)).unwrap();
    let a = arena.var(a_sym);
    // a^exp by a linear chain of multiplications (width holds it, no wraparound).
    let mut power = a;
    for _ in 1..exp {
        power = arena.bv_mul(power, a).unwrap();
    }
    let p_c = arena.bv_const(width, p).unwrap();
    let power_mod = arena.bv_urem(power, p_c).unwrap();
    let one = arena.bv_const(width, 1).unwrap();
    let is_one = arena.eq(power_mod, one).unwrap();
    let zero = arena.bv_const(width, 0).unwrap();
    let a_is_zero = arena.eq(a, zero).unwrap();
    let a_nonzero = arena.not(a_is_zero).unwrap();
    let a_lt_p = arena.bv_ult(a, p_c).unwrap();
    let in_units = arena.and(a_nonzero, a_lt_p).unwrap();
    let body = arena.implies(in_units, is_one).unwrap();
    let claim = arena.forall(a_sym, body).unwrap();
    let negation = arena.not(claim).unwrap();
    closed_unsat(
        arena,
        format!("predicate/fermat_little_p{p}"),
        width,
        negation,
    )
}

/// Packages a closed Boolean term (the negation of a quantified theorem) as an
/// UNSAT scenario. The formula is closed, so the single empty assignment
/// falsifies it; we record the enumeration over the declared (bound) symbols.
fn closed_unsat(
    arena: TermArena,
    label: String,
    width: u32,
    negation: axeyum_ir::TermId,
) -> Scenario {
    let symbol_bits: u32 = arena
        .symbols()
        .map(|(_, _, sort)| match sort {
            Sort::BitVec(w) => w,
            _ => 0,
        })
        .sum();
    let mut builder = Query::builder(&arena);
    builder.assert(negation).unwrap();
    let query = builder.build();
    Scenario {
        name: label,
        family: Family::Predicate,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << symbol_bits,
            },
        },
    }
}

/// A deterministic catalog of predicate-logic scenarios.
pub fn predicate_catalog() -> Vec<Scenario> {
    vec![
        forall_additive_identity(4),
        forall_exists_inverse(4),
        exists_square_root(4),
        fermat_little_theorem(3),
        fermat_little_theorem(5),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn predicate_catalog_self_checks() {
        for scenario in predicate_catalog() {
            assert_eq!(scenario.family, Family::Predicate);
            scenario.self_check().unwrap_or_else(|e| {
                panic!(
                    "predicate scenario {} failed self-check: {e}",
                    scenario.name
                )
            });
        }
    }

    #[test]
    fn quantifier_alternation_is_a_theorem() {
        // ∀x ∃y. x + y = 0 holds over any BitVec domain.
        forall_exists_inverse(4).self_check().unwrap();
    }
}
