//! Rational-number scenarios: exact ordered-field facts over `QF_LRA`.
//!
//! Exercises the
//! [rationals](../../../docs/curriculum/01-number-systems/rationals.md) node:
//! density (the midpoint strictly between two rationals), the mediant
//! inequality, exact 2×2 linear-system solving, and an order-trichotomy
//! instance — the facts the exact-rational simplex decides. Every scenario is
//! satisfiable by construction with an exact rational witness verified by the
//! evaluator, the same discipline as [`crate::reals`]. Oracle-free per
//! ADR-0008.

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
        family: Family::Rational,
        width: 0,
        seed,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// A small rational with numerator in `[-8, 8]` and denominator in `{1, 2, 3, 4}`.
fn small_rational(rng: &mut SplitMix64) -> Rational {
    let num = i128::try_from(rng.next_u128() % 17).unwrap() - 8;
    let den = [1i128, 2, 3, 4][usize::try_from(rng.next_u128() % 4).unwrap()];
    Rational::new(num, den)
}

/// **Density**: between two distinct rationals `a < b` lies their midpoint.
/// Pins `a` and `b` to random rationals and constrains a fresh `m` by
/// `a < m ∧ m < b ∧ m + m = a + b`; the witness is the exact midpoint.
///
/// # Panics
///
/// Panics on arena corruption.
pub fn density_midpoint(seed: u64) -> Scenario {
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    let mut lo = small_rational(&mut rng);
    let mut hi = small_rational(&mut rng);
    if lo == hi {
        hi = lo + Rational::integer(1);
    }
    if hi < lo {
        std::mem::swap(&mut lo, &mut hi);
    }
    let mid = (lo + hi) / Rational::integer(2);

    let a_sym = arena.declare("a", Sort::Real).unwrap();
    let b_sym = arena.declare("b", Sort::Real).unwrap();
    let m_sym = arena.declare("m", Sort::Real).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let m = arena.var(m_sym);
    witness.set(a_sym, Value::Real(lo));
    witness.set(b_sym, Value::Real(hi));
    witness.set(m_sym, Value::Real(mid));

    let lo_const = arena.real_const(lo);
    let hi_const = arena.real_const(hi);
    let pin_a = arena.eq(a, lo_const).unwrap();
    let pin_b = arena.eq(b, hi_const).unwrap();
    let below = arena.real_lt(a, m).unwrap();
    let above = arena.real_lt(m, b).unwrap();
    let doubled = arena.real_add(m, m).unwrap();
    let sum = arena.real_add(a, b).unwrap();
    let pinned_mid = arena.eq(doubled, sum).unwrap();

    finish(
        arena,
        vec![pin_a, pin_b, below, above, pinned_mid],
        witness,
        format!("rational/density_midpoint_{seed:#018x}"),
        seed,
    )
}

/// **The mediant inequality**: for positive denominators with `p/q < r/s`, the
/// mediant `(p+r)/(q+s)` lies strictly between. Constrains a fresh `x` by
/// `(q+s)·x = p+r` plus the strict bounds; the witness is the exact mediant.
///
/// # Panics
///
/// Panics on arena corruption.
pub fn mediant_between(seed: u64) -> Scenario {
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    // num_lo/den_lo < num_hi/den_hi with positive denominators: draw and
    // order two distinct fractions.
    let den_first = 1 + i128::try_from(rng.next_u128() % 4).unwrap();
    let den_second = 1 + i128::try_from(rng.next_u128() % 4).unwrap();
    let mut num_first = i128::try_from(rng.next_u128() % 13).unwrap() - 6;
    let num_second = i128::try_from(rng.next_u128() % 13).unwrap() - 6;
    if Rational::new(num_first, den_first) == Rational::new(num_second, den_second) {
        num_first -= 1;
    }
    let (num_lo, den_lo, num_hi, den_hi) =
        if Rational::new(num_first, den_first) < Rational::new(num_second, den_second) {
            (num_first, den_first, num_second, den_second)
        } else {
            (num_second, den_second, num_first, den_first)
        };
    let mediant = Rational::new(num_lo + num_hi, den_lo + den_hi);

    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    witness.set(x_sym, Value::Real(mediant));

    let weight = arena.real_const(Rational::integer(den_lo + den_hi));
    let target = arena.real_const(Rational::integer(num_lo + num_hi));
    let scaled = arena.real_mul(weight, x).unwrap();
    let pinned = arena.eq(scaled, target).unwrap();
    let lo_const = arena.real_const(Rational::new(num_lo, den_lo));
    let hi_const = arena.real_const(Rational::new(num_hi, den_hi));
    let above = arena.real_lt(lo_const, x).unwrap();
    let below = arena.real_lt(x, hi_const).unwrap();

    finish(
        arena,
        vec![pinned, above, below],
        witness,
        format!("rational/mediant_between_{seed:#018x}"),
        seed,
    )
}

/// **Exact 2×2 linear system**: integer coefficients with nonzero determinant
/// around a chosen rational solution `(x, y)`; both equations are asserted and
/// the witness is the exact solution.
///
/// # Panics
///
/// Panics on arena corruption.
pub fn exact_linear_solution(seed: u64) -> Scenario {
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    let x_val = small_rational(&mut rng);
    let y_val = small_rational(&mut rng);
    // Integer coefficient rows with nonzero determinant.
    let a11 = 1 + i128::try_from(rng.next_u128() % 4).unwrap();
    let a12 = i128::try_from(rng.next_u128() % 4).unwrap();
    let a21 = i128::try_from(rng.next_u128() % 4).unwrap();
    let mut a22 = 1 + i128::try_from(rng.next_u128() % 4).unwrap();
    if a11 * a22 == a12 * a21 {
        a22 += 1;
    }
    assert!(a11 * a22 != a12 * a21, "determinant must be nonzero");

    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let y_sym = arena.declare("y", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    witness.set(x_sym, Value::Real(x_val));
    witness.set(y_sym, Value::Real(y_val));

    let mut goals = Vec::new();
    for (coeff_x, coeff_y) in [(a11, a12), (a21, a22)] {
        let rhs = Rational::integer(coeff_x) * x_val + Rational::integer(coeff_y) * y_val;
        let x_weight = arena.real_const(Rational::integer(coeff_x));
        let y_weight = arena.real_const(Rational::integer(coeff_y));
        let weighted_x = arena.real_mul(x_weight, x).unwrap();
        let weighted_y = arena.real_mul(y_weight, y).unwrap();
        let lhs = arena.real_add(weighted_x, weighted_y).unwrap();
        let rhs_const = arena.real_const(rhs);
        goals.push(arena.eq(lhs, rhs_const).unwrap());
    }

    finish(
        arena,
        goals,
        witness,
        format!("rational/exact_linear_solution_{seed:#018x}"),
        seed,
    )
}

/// **Trichotomy instance**: a rational is negative, zero, or positive —
/// exactly one holds. Pins `x` to a random rational and asserts the
/// exactly-one structure over the three order atoms; the witness is the pin.
///
/// # Panics
///
/// Panics on arena corruption.
pub fn trichotomy_case(seed: u64) -> Scenario {
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    let value = small_rational(&mut rng);
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    witness.set(x_sym, Value::Real(value));

    let pin_const = arena.real_const(value);
    let pinned = arena.eq(x, pin_const).unwrap();
    let zero = arena.real_const(Rational::zero());
    let negative = arena.real_lt(x, zero).unwrap();
    let is_zero = arena.eq(x, zero).unwrap();
    let positive = arena.real_gt(x, zero).unwrap();

    let neg_or_zero = arena.or(negative, is_zero).unwrap();
    let some = arena.or(neg_or_zero, positive).unwrap();
    let neg_and_zero = arena.and(negative, is_zero).unwrap();
    let neg_and_pos = arena.and(negative, positive).unwrap();
    let zero_and_pos = arena.and(is_zero, positive).unwrap();
    let no_neg_zero = arena.not(neg_and_zero).unwrap();
    let no_neg_pos = arena.not(neg_and_pos).unwrap();
    let no_zero_pos = arena.not(zero_and_pos).unwrap();
    let pair_a = arena.and(no_neg_zero, no_neg_pos).unwrap();
    let exclusive = arena.and(pair_a, no_zero_pos).unwrap();
    let exactly_one = arena.and(some, exclusive).unwrap();

    finish(
        arena,
        vec![pinned, exactly_one],
        witness,
        format!("rational/trichotomy_case_{seed:#018x}"),
        seed,
    )
}

/// A deterministic catalog of rational-number scenarios. Every entry is
/// satisfiable by construction and passes [`Scenario::self_check`].
pub fn rational_catalog() -> Vec<Scenario> {
    let mut scenarios = Vec::new();
    for round in 0..2u64 {
        scenarios.push(density_midpoint(0x7A71_0000 ^ round));
        scenarios.push(mediant_between(0x7A71_1100 ^ round));
        scenarios.push(exact_linear_solution(0x7A71_2200 ^ round));
        scenarios.push(trichotomy_case(0x7A71_3300 ^ round));
    }
    scenarios
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rational_catalog_self_checks() {
        let catalog = rational_catalog();
        assert!(!catalog.is_empty());
        for scenario in catalog {
            assert_eq!(scenario.family, Family::Rational);
            assert!(matches!(scenario.expectation, Expectation::Sat { .. }));
            scenario.self_check().unwrap_or_else(|e| {
                panic!("rational scenario {} failed self-check: {e}", scenario.name)
            });
        }
    }
}
