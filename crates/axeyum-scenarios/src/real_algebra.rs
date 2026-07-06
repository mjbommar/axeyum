//! Real-number scenarios: algebraic (real-closed-field) facts with exact
//! rational witnesses.
//!
//! Exercises the [reals](../../../docs/curriculum/01-number-systems/reals.md)
//! node: the *elementary algebraic* theory of the reals is decidable (Tarski),
//! and its rational-witness slice is exactly checkable today — quadratic roots,
//! an AM–GM instance whose geometric mean is rational by construction, and a
//! nested-interval completeness shadow. Completeness itself (suprema, limits,
//! irrational witnesses) stays Lean-horizon; these scenarios are satisfiable
//! by construction with exact rational witnesses verified by the evaluator.
//! Oracle-free per ADR-0008.

use axeyum_ir::{Assignment, Rational, Sort, TermArena, TermId, Value};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, SplitMix64};

fn finish(
    arena: TermArena,
    goals: Vec<TermId>,
    witness: Assignment,
    name: String,
    seed: u64,
) -> Scenario {
    let mut builder = Query::builder(&arena);
    for goal in goals {
        builder.assert(goal).unwrap();
    }
    let query = builder.build();
    Scenario {
        name,
        family: Family::RealAlgebra,
        width: 0,
        seed,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// A small rational with numerator in `[-6, 6]` and denominator in `{1, 2, 3}`.
fn small_rational(rng: &mut SplitMix64) -> Rational {
    let num = i128::try_from(rng.next_u128() % 13).unwrap() - 6;
    let den = [1i128, 2, 3][usize::try_from(rng.next_u128() % 3).unwrap()];
    Rational::new(num, den)
}

/// **Quadratic root**: a monic quadratic with chosen rational roots
/// `r1 < r2`, asserted as `x·x − (r1+r2)·x + r1·r2 = 0` with `x > r1`; the
/// witness is the larger root `x = r2`.
///
/// # Panics
///
/// Panics on arena corruption.
pub fn quadratic_rational_root(seed: u64) -> Scenario {
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    let mut r1 = small_rational(&mut rng);
    let mut r2 = small_rational(&mut rng);
    if r1 == r2 {
        r2 = r1 + Rational::integer(1);
    }
    if r2 < r1 {
        std::mem::swap(&mut r1, &mut r2);
    }

    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    witness.set(x_sym, Value::Real(r2));

    let square = arena.real_mul(x, x).unwrap();
    let sum_const = arena.real_const(r1 + r2);
    let linear = arena.real_mul(sum_const, x).unwrap();
    let product_const = arena.real_const(r1 * r2);
    let shifted = arena.real_sub(square, linear).unwrap();
    let value = arena.real_add(shifted, product_const).unwrap();
    let zero = arena.real_const(Rational::zero());
    let vanishes = arena.eq(value, zero).unwrap();
    let r1_const = arena.real_const(r1);
    let larger = arena.real_gt(x, r1_const).unwrap();

    finish(
        arena,
        vec![vanishes, larger],
        witness,
        format!("real_algebra/quadratic_rational_root_{seed:#018x}"),
        seed,
    )
}

/// **An AM–GM instance**: for `a = k·m²` and `b = k·n²` the geometric mean
/// `g = k·m·n` is rational, and `g·g = a·b ∧ g ≥ 0 ∧ 2·g ≤ a + b` holds with
/// equality exactly when `m = n`. The witness is the exact geometric mean.
///
/// # Panics
///
/// Panics on arena corruption.
pub fn am_gm_instance(seed: u64) -> Scenario {
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    let scale = Rational::new(
        1 + i128::try_from(rng.next_u128() % 3).unwrap(),
        [1i128, 2][usize::try_from(rng.next_u128() % 2).unwrap()],
    );
    let left_side = Rational::integer(1 + i128::try_from(rng.next_u128() % 3).unwrap());
    let right_side = Rational::integer(1 + i128::try_from(rng.next_u128() % 3).unwrap());
    let first = scale * left_side * left_side;
    let second = scale * right_side * right_side;
    let g_val = scale * left_side * right_side;

    let g_sym = arena.declare("g", Sort::Real).unwrap();
    let g = arena.var(g_sym);
    witness.set(g_sym, Value::Real(g_val));

    let square = arena.real_mul(g, g).unwrap();
    let product_const = arena.real_const(first * second);
    let squares_match = arena.eq(square, product_const).unwrap();
    let zero = arena.real_const(Rational::zero());
    let nonneg = arena.real_ge(g, zero).unwrap();
    let doubled = arena.real_add(g, g).unwrap();
    let sum_const = arena.real_const(first + second);
    let am_gm = arena.real_le(doubled, sum_const).unwrap();

    finish(
        arena,
        vec![squares_match, nonneg, am_gm],
        witness,
        format!("real_algebra/am_gm_instance_{seed:#018x}"),
        seed,
    )
}

/// **Nested intervals** (a bounded completeness shadow): three strictly
/// shrinking rational intervals around a chosen point, with one real `x`
/// asserted to lie in all of them; the witness is the point. The full
/// nested-interval theorem (a point exists for *every* such chain) is the
/// completeness axiom and stays Lean-horizon.
///
/// # Panics
///
/// Panics on arena corruption.
pub fn nested_intervals_point(seed: u64) -> Scenario {
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    let point = small_rational(&mut rng);
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    witness.set(x_sym, Value::Real(point));

    let mut goals = Vec::new();
    for level in 1..=3i128 {
        // Radii 1, 1/2, 1/4 around the point.
        let radius = Rational::new(1, 1 << (level - 1));
        let lo = arena.real_const(point - radius);
        let hi = arena.real_const(point + radius);
        goals.push(arena.real_ge(x, lo).unwrap());
        goals.push(arena.real_le(x, hi).unwrap());
    }

    finish(
        arena,
        goals,
        witness,
        format!("real_algebra/nested_intervals_point_{seed:#018x}"),
        seed,
    )
}

/// A deterministic catalog of real-algebra scenarios. Every entry is
/// satisfiable by construction and passes [`Scenario::self_check`].
pub fn real_algebra_catalog() -> Vec<Scenario> {
    let mut scenarios = Vec::new();
    for round in 0..2u64 {
        scenarios.push(quadratic_rational_root(0x2EA1_0000 ^ round));
        scenarios.push(am_gm_instance(0x2EA1_1100 ^ round));
        scenarios.push(nested_intervals_point(0x2EA1_2200 ^ round));
    }
    scenarios
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn real_algebra_catalog_self_checks() {
        let catalog = real_algebra_catalog();
        assert!(!catalog.is_empty());
        for scenario in catalog {
            assert_eq!(scenario.family, Family::RealAlgebra);
            assert!(matches!(scenario.expectation, Expectation::Sat { .. }));
            scenario.self_check().unwrap_or_else(|e| {
                panic!(
                    "real-algebra scenario {} failed self-check: {e}",
                    scenario.name
                )
            });
        }
    }
}
