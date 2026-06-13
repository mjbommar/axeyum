//! Linear integer arithmetic (`QF_LIA`) scenarios: self-checking constraint
//! systems (ADR-0014).
//!
//! These mirror the integer reasoning a consumer does over loop counters,
//! offsets, and sizes: a handful of integer variables constrained by linear
//! equations, box bounds, and orderings. A concrete witness is chosen first and
//! every constraint is asserted so the witness satisfies it by construction, so
//! the query is satisfiable and self-verifies through the evaluator — exactly
//! like the bit-vector, memory, and function families, now over integers.
//!
//! Values are kept small so they fit the default bounded bit-blasting width and
//! the `i128` evaluator reference range.

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, SplitMix64};

/// Builds a satisfiable linear constraint system over `count` integer
/// variables: each variable is boxed around its witness value, the variables
/// are ordered consistently with the witness, and their sum is pinned to the
/// witness sum. All constraints hold for the chosen witness by construction.
///
/// # Panics
///
/// Panics if `count` is zero or on arena corruption.
pub fn integer_system(count: usize, seed: u64) -> Scenario {
    assert!(count >= 1, "integer_system needs >= 1 variable");
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    // Choose concrete witness values in a small range and declare a variable
    // for each.
    let mut values = Vec::with_capacity(count);
    let mut terms = Vec::with_capacity(count);
    for i in 0..count {
        let sym = arena.declare(&format!("n{i}"), Sort::Int).unwrap();
        let value = small_int(&mut rng);
        witness.set(sym, Value::Int(value));
        terms.push(arena.var(sym));
        values.push(value);
    }

    let mut goals = Vec::new();

    // Box each variable: witness - slack <= n_i <= witness + slack.
    for (i, &value) in values.iter().enumerate() {
        let slack = i128::try_from(rng.next_u128() % 5).unwrap();
        let lo = arena.int_const(value - slack);
        let hi = arena.int_const(value + slack);
        goals.push(arena.int_ge(terms[i], lo).unwrap());
        goals.push(arena.int_le(terms[i], hi).unwrap());
    }

    // Order consecutive variables consistently with the witness.
    for i in 0..count - 1 {
        let rel = match values[i].cmp(&values[i + 1]) {
            std::cmp::Ordering::Less => arena.int_lt(terms[i], terms[i + 1]).unwrap(),
            std::cmp::Ordering::Greater => arena.int_gt(terms[i], terms[i + 1]).unwrap(),
            std::cmp::Ordering::Equal => arena.eq(terms[i], terms[i + 1]).unwrap(),
        };
        goals.push(rel);
    }

    // Pin the sum of all variables to the witness sum.
    let mut sum_term = terms[0];
    for &var in &terms[1..] {
        sum_term = arena.int_add(sum_term, var).unwrap();
    }
    let sum_value: i128 = values.iter().sum();
    let sum_const = arena.int_const(sum_value);
    goals.push(arena.eq(sum_term, sum_const).unwrap());

    finish(
        arena,
        goals,
        witness,
        format!("integer/system_n{count}_{seed:#018x}"),
        seed,
    )
}

/// Builds a satisfiable single linear equation `a*x + b*y == c` (with `a`, `b`
/// constant coefficients), satisfiable by the chosen witness `(x, y)`.
///
/// # Panics
///
/// Panics on arena corruption.
pub fn integer_equation(seed: u64) -> Scenario {
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let y_sym = arena.declare("y", Sort::Int).unwrap();
    let x_val = small_int(&mut rng);
    let y_val = small_int(&mut rng);
    witness.set(x_sym, Value::Int(x_val));
    witness.set(y_sym, Value::Int(y_val));
    let x_term = arena.var(x_sym);
    let y_term = arena.var(y_sym);

    // Small non-zero coefficients.
    let coeff_a = 1 + i128::try_from(rng.next_u128() % 4).unwrap();
    let coeff_b = 1 + i128::try_from(rng.next_u128() % 4).unwrap();
    let a_const = arena.int_const(coeff_a);
    let b_const = arena.int_const(coeff_b);
    let ax = arena.int_mul(a_const, x_term).unwrap();
    let by = arena.int_mul(b_const, y_term).unwrap();
    let lhs = arena.int_add(ax, by).unwrap();
    let rhs = arena.int_const(coeff_a * x_val + coeff_b * y_val);
    let eq = arena.eq(lhs, rhs).unwrap();

    // Box both variables tightly around the witness. This keeps the *only*
    // in-range models near the witness, so the bounded bit-blaster cannot pick
    // an overflowing model — the linear equation alone is too loose and a
    // wrapped bit-vector solution would (correctly) be reported `unknown`.
    let mut goals = vec![eq];
    for (var, value) in [(x_term, x_val), (y_term, y_val)] {
        let lo = arena.int_const(value - 3);
        let hi = arena.int_const(value + 3);
        goals.push(arena.int_ge(var, lo).unwrap());
        goals.push(arena.int_le(var, hi).unwrap());
    }

    finish(
        arena,
        goals,
        witness,
        format!("integer/equation_{seed:#018x}"),
        seed,
    )
}

/// A deterministic catalog of `QF_LIA` scenarios. Every entry is satisfiable by
/// construction and passes [`Scenario::self_check`]; values are small enough for
/// the default bounded bit-blasting width.
pub fn integer_catalog() -> Vec<Scenario> {
    let mut scenarios = Vec::new();
    for count in [1usize, 2, 3, 5] {
        scenarios.push(integer_system(count, 0x1A7E_0000 ^ (count as u64)));
    }
    for round in 0..3u64 {
        scenarios.push(integer_equation(0x5EED_1A00 ^ round));
    }
    scenarios
}

/// A small signed integer in roughly `[-20, 20]`.
fn small_int(rng: &mut SplitMix64) -> i128 {
    i128::try_from(rng.next_u128() % 41).unwrap() - 20
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
        family: Family::Integer,
        width: 0,
        seed,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

#[cfg(test)]
mod tests {
    use super::{integer_catalog, integer_equation, integer_system};
    use crate::{Expectation, Family};

    #[test]
    fn generators_self_check() {
        let scenarios = [
            integer_system(1, 0x11),
            integer_system(5, 0x22),
            integer_equation(0x33),
        ];
        for scenario in scenarios {
            assert_eq!(scenario.family, Family::Integer);
            assert!(matches!(scenario.expectation, Expectation::Sat { .. }));
            scenario
                .self_check()
                .unwrap_or_else(|error| panic!("{} failed self-check: {error}", scenario.name));
        }
    }

    #[test]
    fn catalog_is_nonempty_and_self_checks() {
        let catalog = integer_catalog();
        assert!(!catalog.is_empty());
        for scenario in catalog {
            scenario
                .self_check()
                .unwrap_or_else(|error| panic!("{} failed self-check: {error}", scenario.name));
        }
    }
}
