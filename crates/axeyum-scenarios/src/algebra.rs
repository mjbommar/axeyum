//! Abstract-algebra scenarios: group axioms over ℤ/2ʷℤ, checked symbolically.
//!
//! The integers mod `2ʷ` form a group under addition; bit-vector addition *is*
//! that group operation, so the [group axioms](../../../docs/curriculum/02-structures/groups.md)
//! become exhaustively checkable bit-vector identities over symbolic elements:
//! associativity and the existence of additive inverses. The same lens exposes
//! *why subtraction is not a group operation* — it is not associative, witnessed
//! by a concrete counterexample.
//!
//! All oracle-free per ADR-0008 (UNSAT by exhaustive enumeration; the
//! non-associativity counterexample is SAT-by-witness), inside the BV subset.

use axeyum_ir::{Assignment, Sort, TermArena, Value};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, UnsatEvidence};

/// Associativity of addition in ℤ/2ʷℤ: `(a + b) + c = a + (b + c)`. The negation
/// is unsatisfiable, proven exhaustively (3 symbols).
///
/// # Panics
///
/// Panics if `3 * width` exceeds the exhaustive budget or on arena corruption.
pub fn addition_associative(width: u32) -> Scenario {
    assert!(
        3 * width <= 20,
        "addition_associative stays inside the budget"
    );
    let mut arena = TermArena::new();
    let a = arena
        .declare("a", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let b = arena
        .declare("b", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let c = arena
        .declare("c", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let ab = arena.bv_add(a, b).unwrap();
    let lhs = arena.bv_add(ab, c).unwrap();
    let bc = arena.bv_add(b, c).unwrap();
    let rhs = arena.bv_add(a, bc).unwrap();
    let equal = arena.eq(lhs, rhs).unwrap();
    let differ = arena.not(equal).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(differ).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("algebra/addition_associative_w{width}"),
        family: Family::Algebra,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << (3 * width),
            },
        },
    }
}

/// Existence of additive inverses in ℤ/2ʷℤ: `a + (−a) = 0` for every `a`. The
/// negation is unsatisfiable, proven exhaustively (1 symbol).
///
/// # Panics
///
/// Panics if `width` exceeds the exhaustive budget or on arena corruption.
pub fn additive_inverse(width: u32) -> Scenario {
    assert!(width <= 20, "additive_inverse stays inside the budget");
    let mut arena = TermArena::new();
    let a = arena
        .declare("a", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let neg_a = arena.bv_neg(a).unwrap();
    let sum = arena.bv_add(a, neg_a).unwrap();
    let zero = arena.bv_const(width, 0).unwrap();
    let is_zero = arena.eq(sum, zero).unwrap();
    let nonzero = arena.not(is_zero).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(nonzero).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("algebra/additive_inverse_w{width}"),
        family: Family::Algebra,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << width,
            },
        },
    }
}

/// Subtraction is **not** associative — so it is not a group operation. This is
/// satisfiable: there exist `a, b, c` with `(a − b) − c ≠ a − (b − c)`,
/// witnessed by `(0, 1, 1)` (the counterexample, since `(0−1)−1 = 2ʷ−2 ≠ 0 =
/// 0−(1−1)` for `w ≥ 2`).
///
/// # Panics
///
/// Panics if `width` is outside `2..=32` or on arena corruption.
pub fn subtraction_not_associative(width: u32) -> Scenario {
    assert!(
        (2..=32).contains(&width),
        "needs width >= 2 for the counterexample"
    );
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(width)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(width)).unwrap();
    let c_sym = arena.declare("c", Sort::BitVec(width)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let c = arena.var(c_sym);
    let ab = arena.bv_sub(a, b).unwrap();
    let lhs = arena.bv_sub(ab, c).unwrap();
    let bc = arena.bv_sub(b, c).unwrap();
    let rhs = arena.bv_sub(a, bc).unwrap();
    let equal = arena.eq(lhs, rhs).unwrap();
    let differ = arena.not(equal).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(differ).unwrap();
    let query = builder.build();

    let mut witness = Assignment::new();
    witness.set(a_sym, Value::Bv { width, value: 0 });
    witness.set(b_sym, Value::Bv { width, value: 1 });
    witness.set(c_sym, Value::Bv { width, value: 1 });

    Scenario {
        name: format!("algebra/subtraction_not_associative_w{width}"),
        family: Family::Algebra,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// ℤ/2ʷℤ is a **ring but not an integral domain**: it has zero divisors. This is
/// satisfiable — there exist nonzero `a, b` with `a · b = 0` — witnessed by
/// `a = 2, b = 2^(w−1)` (so `a·b = 2ʷ ≡ 0`).
///
/// # Panics
///
/// Panics if `width` is outside `2..=32` or on arena corruption.
pub fn zero_divisor(width: u32) -> Scenario {
    assert!((2..=32).contains(&width), "zero_divisor needs width 2..=32");
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(width)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(width)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let zero = arena.bv_const(width, 0).unwrap();
    let a_eq_zero = arena.eq(a, zero).unwrap();
    let a_nonzero = arena.not(a_eq_zero).unwrap();
    let b_eq_zero = arena.eq(b, zero).unwrap();
    let b_nonzero = arena.not(b_eq_zero).unwrap();
    let product = arena.bv_mul(a, b).unwrap();
    let product_zero = arena.eq(product, zero).unwrap();
    let a_b_nonzero = arena.and(a_nonzero, b_nonzero).unwrap();
    let goal = arena.and(a_b_nonzero, product_zero).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(goal).unwrap();
    let query = builder.build();

    let mut witness = Assignment::new();
    witness.set(a_sym, Value::Bv { width, value: 2 });
    witness.set(
        b_sym,
        Value::Bv {
            width,
            value: 1u128 << (width - 1),
        },
    );

    Scenario {
        name: format!("algebra/zero_divisor_w{width}"),
        family: Family::Algebra,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// ℤ/2ʷℤ is **not a field**: an even element has no multiplicative inverse. The
/// claim `∃ b. 2·b = 1 (mod 2ʷ)` is unsatisfiable (the left side is always
/// even), proven exhaustively (1 symbol).
///
/// # Panics
///
/// Panics if `width` exceeds the exhaustive budget or on arena corruption.
pub fn field_failure_even(width: u32) -> Scenario {
    assert!(
        (1..=20).contains(&width),
        "field_failure stays inside the budget"
    );
    let mut arena = TermArena::new();
    let b = arena
        .declare("b", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let two = arena.bv_const(width, 2).unwrap();
    let product = arena.bv_mul(two, b).unwrap();
    let one = arena.bv_const(width, 1).unwrap();
    let is_inverse = arena.eq(product, one).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(is_inverse).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("algebra/field_failure_even_w{width}"),
        family: Family::Algebra,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << width,
            },
        },
    }
}

/// 𝔽₇ is a **field**: every nonzero element is invertible. So "there is a
/// nonzero `a < 7` with no inverse mod 7" — `∃a≠0. a<7 ∧ ∀b<7. a·b ≢ 1 (mod 7)` —
/// is unsatisfiable, proven exhaustively over `a` (the `∀b` is decided by
/// finite-domain quantifier evaluation).
///
/// # Panics
///
/// Panics if `width` is outside `6..=10` or on arena corruption.
pub fn prime_field_all_invertible(width: u32) -> Scenario {
    assert!((6..=10).contains(&width), "prime_field stays inside the budget");
    let (_a_sym, query, arena) = no_inverse_query(width, 7);
    Scenario {
        name: format!("algebra/prime_field_all_invertible_w{width}"),
        family: Family::Algebra,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive { cases: 1u64 << width },
        },
    }
}

/// ℤ/6ℤ is **not a field**: `2` has no multiplicative inverse. So
/// `∃a≠0. a<6 ∧ ∀b<6. a·b ≢ 1 (mod 6)` is satisfiable, witnessed by `a = 2`.
///
/// # Panics
///
/// Panics if `width` is outside `6..=10` or on arena corruption.
pub fn composite_modulus_non_invertible(width: u32) -> Scenario {
    assert!((6..=10).contains(&width), "composite_modulus stays inside the budget");
    let (a_sym, query, arena) = no_inverse_query(width, 6);
    let mut witness = Assignment::new();
    witness.set(a_sym, Value::Bv { width, value: 2 });
    Scenario {
        name: format!("algebra/composite_modulus_non_invertible_w{width}"),
        family: Family::Algebra,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// Builds the query `∃a≠0. a<m ∧ ∀b. (b<m ⇒ a·b ≢ 1 (mod m))` over `width`-bit
/// arithmetic; returns the free candidate symbol `a`, the query, and the arena.
/// `b` is universally bound (decided by finite-domain enumeration).
fn no_inverse_query(width: u32, m: u128) -> (axeyum_ir::SymbolId, Query, TermArena) {
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(width)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(width)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let m_c = arena.bv_const(width, m).unwrap();
    let one = arena.bv_const(width, 1).unwrap();
    let zero = arena.bv_const(width, 0).unwrap();
    let prod = arena.bv_mul(a, b).unwrap();
    let prod_mod = arena.bv_urem(prod, m_c).unwrap();
    let is_one = arena.eq(prod_mod, one).unwrap();
    let not_one = arena.not(is_one).unwrap();
    let b_lt_m = arena.bv_ult(b, m_c).unwrap();
    let body = arena.implies(b_lt_m, not_one).unwrap();
    let no_inverse = arena.forall(b_sym, body).unwrap();
    let a_is_zero = arena.eq(a, zero).unwrap();
    let a_nonzero = arena.not(a_is_zero).unwrap();
    let a_lt_m = arena.bv_ult(a, m_c).unwrap();
    let a_constraints = arena.and(a_nonzero, a_lt_m).unwrap();
    let claim = arena.and(a_constraints, no_inverse).unwrap();
    let mut builder = Query::builder(&arena);
    builder.assert(claim).unwrap();
    let query = builder.build();
    (a_sym, query, arena)
}

/// A deterministic catalog of abstract-algebra scenarios.
pub fn algebra_catalog() -> Vec<Scenario> {
    vec![
        addition_associative(4),
        addition_associative(6),
        additive_inverse(8),
        additive_inverse(16),
        subtraction_not_associative(8),
        zero_divisor(8),
        field_failure_even(8),
        field_failure_even(16),
        prime_field_all_invertible(6),
        composite_modulus_non_invertible(6),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn algebra_catalog_self_checks() {
        for scenario in algebra_catalog() {
            assert_eq!(scenario.family, Family::Algebra);
            scenario.self_check().unwrap_or_else(|e| {
                panic!("algebra scenario {} failed self-check: {e}", scenario.name)
            });
        }
    }

    #[test]
    fn subtraction_counterexample_is_genuine() {
        // The (0,1,1) witness really does break associativity.
        let scenario = subtraction_not_associative(8);
        assert!(matches!(scenario.expectation, Expectation::Sat { .. }));
        scenario.self_check().unwrap();
    }
}
