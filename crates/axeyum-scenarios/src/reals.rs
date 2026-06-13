//! Linear real arithmetic (`QF_LRA`) scenarios: self-checking constraint
//! systems over exact rationals (ADR-0015).
//!
//! These mirror the real reasoning a consumer does over ratios, rates, and
//! continuous quantities: a handful of real variables boxed around a rational
//! witness, ordered consistently, and tied by a linear equation. A concrete
//! rational witness is chosen first and every constraint is asserted so the
//! witness satisfies it by construction, so the query is satisfiable and
//! self-verifies through the evaluator — like the other families, now over
//! exact rationals.

use axeyum_ir::{Assignment, Rational, Sort, TermArena, TermId, Value};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, SplitMix64};

/// Builds a satisfiable linear real constraint system over `count` variables:
/// each variable is boxed around its rational witness, the variables are ordered
/// consistently with the witness, and their sum is pinned to the witness sum.
///
/// # Panics
///
/// Panics if `count` is zero or on arena corruption.
pub fn real_system(count: usize, seed: u64) -> Scenario {
    assert!(count >= 1, "real_system needs >= 1 variable");
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    let mut values = Vec::with_capacity(count);
    let mut terms = Vec::with_capacity(count);
    for i in 0..count {
        let sym = arena.declare(&format!("r{i}"), Sort::Real).unwrap();
        let value = small_rational(&mut rng);
        witness.set(sym, Value::Real(value));
        terms.push(arena.var(sym));
        values.push(value);
    }

    let mut goals = Vec::new();

    // Box each variable: witness - 1 <= r_i <= witness + 1.
    for (i, &value) in values.iter().enumerate() {
        let lo = arena.real_const(value - Rational::integer(1));
        let hi = arena.real_const(value + Rational::integer(1));
        goals.push(arena.real_ge(terms[i], lo).unwrap());
        goals.push(arena.real_le(terms[i], hi).unwrap());
    }

    // Order consecutive variables consistently with the witness.
    for i in 0..count - 1 {
        let rel = match values[i].cmp(&values[i + 1]) {
            std::cmp::Ordering::Less => arena.real_lt(terms[i], terms[i + 1]).unwrap(),
            std::cmp::Ordering::Greater => arena.real_gt(terms[i], terms[i + 1]).unwrap(),
            std::cmp::Ordering::Equal => arena.eq(terms[i], terms[i + 1]).unwrap(),
        };
        goals.push(rel);
    }

    // Pin the sum of all variables to the witness sum.
    let mut sum_term = terms[0];
    for &term in &terms[1..] {
        sum_term = arena.real_add(sum_term, term).unwrap();
    }
    let sum_value = values
        .iter()
        .copied()
        .fold(Rational::zero(), |acc, value| acc + value);
    let sum_const = arena.real_const(sum_value);
    goals.push(arena.eq(sum_term, sum_const).unwrap());

    finish(
        arena,
        goals,
        witness,
        format!("real/system_n{count}_{seed:#018x}"),
        seed,
    )
}

/// Builds a satisfiable scaled equation `a*x == b` over reals, pinning the
/// (generally fractional) witness `x = b/a`, plus a sign hint.
///
/// # Panics
///
/// Panics on arena corruption.
pub fn real_ratio_equation(seed: u64) -> Scenario {
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    // a in 1..=4, b in -6..=6; witness x = b/a (exact rational).
    let a = 1 + i128::try_from(rng.next_u128() % 4).unwrap();
    let b = i128::try_from(rng.next_u128() % 13).unwrap() - 6;
    let xv = Rational::new(b, a);
    witness.set(x_sym, Value::Real(xv));

    let a_const = arena.real_const(Rational::integer(a));
    let b_const = arena.real_const(Rational::integer(b));
    let ax = arena.real_mul(a_const, x).unwrap();
    let eq = arena.eq(ax, b_const).unwrap();

    let zero = arena.real_const(Rational::zero());
    let hint = if xv < Rational::zero() {
        arena.real_lt(x, zero).unwrap()
    } else {
        arena.real_ge(x, zero).unwrap()
    };

    finish(
        arena,
        vec![eq, hint],
        witness,
        format!("real/ratio_eq_{seed:#018x}"),
        seed,
    )
}

/// A deterministic catalog of `QF_LRA` scenarios. Every entry is satisfiable by
/// construction and passes [`Scenario::self_check`].
pub fn real_catalog() -> Vec<Scenario> {
    let mut scenarios = Vec::new();
    for count in [1usize, 2, 3, 5] {
        scenarios.push(real_system(count, 0x4EA1_0000 ^ (count as u64)));
    }
    for round in 0..3u64 {
        scenarios.push(real_ratio_equation(0x4EA1_2A00 ^ round));
    }
    scenarios
}

/// A small rational with numerator in `[-8, 8]` and denominator in `{1, 2, 4}`.
fn small_rational(rng: &mut SplitMix64) -> Rational {
    let num = i128::try_from(rng.next_u128() % 17).unwrap() - 8;
    let den = [1i128, 2, 4][usize::try_from(rng.next_u128() % 3).unwrap()];
    Rational::new(num, den)
}

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
        family: Family::Real,
        width: 0,
        seed,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

#[cfg(test)]
mod tests {
    use super::{real_catalog, real_ratio_equation, real_system};
    use crate::{Expectation, Family};

    #[test]
    fn generators_self_check() {
        let scenarios = [
            real_system(1, 0x71),
            real_system(5, 0x72),
            real_ratio_equation(0x73),
        ];
        for scenario in scenarios {
            assert_eq!(scenario.family, Family::Real);
            assert!(matches!(scenario.expectation, Expectation::Sat { .. }));
            scenario
                .self_check()
                .unwrap_or_else(|error| panic!("{} failed self-check: {error}", scenario.name));
        }
    }

    #[test]
    fn catalog_is_nonempty_and_self_checks() {
        let catalog = real_catalog();
        assert!(!catalog.is_empty());
        for scenario in catalog {
            scenario
                .self_check()
                .unwrap_or_else(|error| panic!("{} failed self-check: {error}", scenario.name));
        }
    }
}
