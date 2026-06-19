//! Polynomial scenarios over bit-vectors: the
//! [polynomials](../../../docs/curriculum/02-structures/polynomials.md) node.
//!
//! Fixed-degree polynomial *identities* hold in any commutative ring, so they
//! hold mod `2ʷ` and their negations are unsatisfiable — exhaustively checkable
//! over small bit-vector inputs. A polynomial *root* is satisfiable with the
//! root as witness. Oracle-free per ADR-0008, inside the BV lowering subset.

use axeyum_ir::{Assignment, Sort, TermArena, Value};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, UnsatEvidence};

/// Packages the negation of an identity over two `width`-bit variables as an
/// UNSAT scenario proven exhaustively.
fn unsat_two_var(
    mut arena: TermArena,
    label: String,
    width: u32,
    lhs: axeyum_ir::TermId,
    rhs: axeyum_ir::TermId,
) -> Scenario {
    let equal = arena.eq(lhs, rhs).unwrap();
    let differ = arena.not(equal).unwrap();
    let mut builder = Query::builder(&arena);
    builder.assert(differ).unwrap();
    let query = builder.build();
    Scenario {
        name: label,
        family: Family::Polynomial,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << (2 * width),
            },
        },
    }
}

/// Negation of the binomial square `(x + y)² = x² + 2xy + y²` — unsatisfiable,
/// proven exhaustively (2 symbols).
///
/// # Panics
///
/// Panics if `2 * width` exceeds the exhaustive budget or on arena corruption.
pub fn binomial_square(width: u32) -> Scenario {
    assert!(2 * width <= 20, "binomial_square stays inside the budget");
    let mut arena = TermArena::new();
    let x = arena
        .declare("x", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let y = arena
        .declare("y", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let sum = arena.bv_add(x, y).unwrap();
    let lhs = arena.bv_mul(sum, sum).unwrap();
    let x2 = arena.bv_mul(x, x).unwrap();
    let y2 = arena.bv_mul(y, y).unwrap();
    let xy = arena.bv_mul(x, y).unwrap();
    let two = arena.bv_const(width, 2).unwrap();
    let two_xy = arena.bv_mul(two, xy).unwrap();
    let x2_plus_2xy = arena.bv_add(x2, two_xy).unwrap();
    let rhs = arena.bv_add(x2_plus_2xy, y2).unwrap();
    unsat_two_var(
        arena,
        format!("polynomial/binomial_square_w{width}"),
        width,
        lhs,
        rhs,
    )
}

/// Negation of the difference of squares `x² − y² = (x − y)(x + y)` —
/// unsatisfiable, proven exhaustively (2 symbols).
///
/// # Panics
///
/// Panics if `2 * width` exceeds the exhaustive budget or on arena corruption.
pub fn difference_of_squares(width: u32) -> Scenario {
    assert!(
        2 * width <= 20,
        "difference_of_squares stays inside the budget"
    );
    let mut arena = TermArena::new();
    let x = arena
        .declare("x", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let y = arena
        .declare("y", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let x2 = arena.bv_mul(x, x).unwrap();
    let y2 = arena.bv_mul(y, y).unwrap();
    let lhs = arena.bv_sub(x2, y2).unwrap();
    let diff = arena.bv_sub(x, y).unwrap();
    let sum = arena.bv_add(x, y).unwrap();
    let rhs = arena.bv_mul(diff, sum).unwrap();
    unsat_two_var(
        arena,
        format!("polynomial/difference_of_squares_w{width}"),
        width,
        lhs,
        rhs,
    )
}

/// A satisfiable polynomial root: `x² − 5x + 6 = 0` has the root `x = 2`
/// (also `x = 3`), carried as witness. (`width ≥ 4` so the coefficients fit.)
///
/// # Panics
///
/// Panics if `width` is outside `4..=32` or on arena corruption.
pub fn quadratic_root(width: u32) -> Scenario {
    assert!(
        (4..=32).contains(&width),
        "quadratic_root supports widths 4..=32"
    );
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    let x2 = arena.bv_mul(x, x).unwrap();
    let five = arena.bv_const(width, 5).unwrap();
    let five_x = arena.bv_mul(five, x).unwrap();
    let six = arena.bv_const(width, 6).unwrap();
    let x2_minus_5x = arena.bv_sub(x2, five_x).unwrap();
    let poly = arena.bv_add(x2_minus_5x, six).unwrap();
    let zero = arena.bv_const(width, 0).unwrap();
    let goal = arena.eq(poly, zero).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(goal).unwrap();
    let query = builder.build();

    let mut witness = Assignment::new();
    witness.set(x_sym, Value::Bv { width, value: 2 });

    Scenario {
        name: format!("polynomial/quadratic_root_w{width}"),
        family: Family::Polynomial,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// The **factor theorem** in identity form: since `2` and `3` are roots of
/// `x² − 5x + 6`, it factors as `(x − 2)(x − 3)` — an identity in any commutative
/// ring, so it holds mod `2ʷ` for every `x`. The negation is unsatisfiable,
/// proven exhaustively (1 symbol).
///
/// # Panics
///
/// Panics if `width` exceeds the exhaustive budget or on arena corruption.
pub fn factorization_identity(width: u32) -> Scenario {
    assert!(
        width <= 20,
        "factorization_identity stays inside the budget"
    );
    let mut arena = TermArena::new();
    let x = arena
        .declare("x", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let x2 = arena.bv_mul(x, x).unwrap();
    let five = arena.bv_const(width, 5).unwrap();
    let five_x = arena.bv_mul(five, x).unwrap();
    let six = arena.bv_const(width, 6).unwrap();
    let x2_minus_5x = arena.bv_sub(x2, five_x).unwrap();
    let lhs = arena.bv_add(x2_minus_5x, six).unwrap();
    let two = arena.bv_const(width, 2).unwrap();
    let three = arena.bv_const(width, 3).unwrap();
    let x_minus_2 = arena.bv_sub(x, two).unwrap();
    let x_minus_3 = arena.bv_sub(x, three).unwrap();
    let rhs = arena.bv_mul(x_minus_2, x_minus_3).unwrap();
    let equal = arena.eq(lhs, rhs).unwrap();
    let differ = arena.not(equal).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(differ).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("polynomial/factorization_identity_w{width}"),
        family: Family::Polynomial,
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

/// **Division with remainder**: dividing `x² + 1` by `x − 1` gives quotient
/// `x + 1` and remainder `2`, i.e. `x² + 1 = (x−1)(x+1) + 2` — a ring identity
/// (holds mod `2ʷ` for every `x`). The negation is unsatisfiable, proven
/// exhaustively (1 symbol).
///
/// # Panics
///
/// Panics if `width` exceeds the exhaustive budget or on arena corruption.
pub fn division_with_remainder_identity(width: u32) -> Scenario {
    assert!(
        width <= 20,
        "division_with_remainder stays inside the budget"
    );
    let mut arena = TermArena::new();
    let x = arena
        .declare("x", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let x2 = arena.bv_mul(x, x).unwrap();
    let one = arena.bv_const(width, 1).unwrap();
    let lhs = arena.bv_add(x2, one).unwrap(); // x² + 1
    let one_b = arena.bv_const(width, 1).unwrap();
    let x_minus_1 = arena.bv_sub(x, one_b).unwrap();
    let one_c = arena.bv_const(width, 1).unwrap();
    let x_plus_1 = arena.bv_add(x, one_c).unwrap();
    let quotient_times_divisor = arena.bv_mul(x_minus_1, x_plus_1).unwrap();
    let two = arena.bv_const(width, 2).unwrap();
    let rhs = arena.bv_add(quotient_times_divisor, two).unwrap(); // (x−1)(x+1) + 2
    let equal = arena.eq(lhs, rhs).unwrap();
    let differ = arena.not(equal).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(differ).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("polynomial/division_with_remainder_w{width}"),
        family: Family::Polynomial,
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

/// A deterministic catalog of polynomial scenarios.
pub fn polynomial_catalog() -> Vec<Scenario> {
    vec![
        binomial_square(8),
        difference_of_squares(8),
        quadratic_root(8),
        quadratic_root(16),
        factorization_identity(8),
        division_with_remainder_identity(8),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn polynomial_catalog_self_checks() {
        for scenario in polynomial_catalog() {
            assert_eq!(scenario.family, Family::Polynomial);
            scenario.self_check().unwrap_or_else(|e| {
                panic!(
                    "polynomial scenario {} failed self-check: {e}",
                    scenario.name
                )
            });
        }
    }

    #[test]
    fn quadratic_root_witness_is_a_root() {
        let scenario = quadratic_root(8);
        assert!(matches!(scenario.expectation, Expectation::Sat { .. }));
        scenario.self_check().unwrap();
    }
}
