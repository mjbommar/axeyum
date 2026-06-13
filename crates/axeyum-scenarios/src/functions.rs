//! Uninterpreted-function (`QF_UFBV`) scenarios: self-checking application
//! traces (ADR-0013).
//!
//! These mirror what a symbolic-execution consumer does when it abstracts an
//! unmodeled subroutine, hash, or syscall as an uninterpreted function `f`: the
//! solver must respect congruence (`x = y -> f(x) = f(y)`) without a bit-precise
//! model. Each scenario fixes a concrete interpretation of `f` (a finite table)
//! and concrete inputs, asserts that every application equals its
//! table value, and carries the table plus inputs as the witness. The query is
//! satisfiable by construction and self-verifies through the evaluator —
//! exactly like the bit-vector and memory families, now over functions.
//!
//! Repeated argument values across applications are intentional: they are what
//! makes the solver's congruence constraints load-bearing, and the table
//! (keyed by argument value) keeps the construction consistent automatically.

use std::collections::BTreeMap;

use axeyum_ir::{Assignment, FuncValue, Sort, TermArena, Value};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, SplitMix64, mask};

/// Builds a satisfiable nested-application chain `f(f(.. f(x) ..))`: each depth
/// asserts the application equals its concretely-computed value. Exercises
/// deeply nested applications over a single unary function.
///
/// # Panics
///
/// Panics if `width` exceeds 64, if `depth` is zero, or on arena corruption.
pub fn function_chain(width: u32, depth: usize, seed: u64) -> Scenario {
    assert!(
        (1..=64).contains(&width),
        "function_chain supports widths 1..=64"
    );
    assert!(depth >= 1, "function_chain needs depth >= 1");
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    let f = arena
        .declare_fun("f", &[Sort::BitVec(width)], Sort::BitVec(width))
        .unwrap();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x_val = rng.next_u128() & mask(width);
    witness.set(x_sym, bv(width, x_val));

    let mut table: BTreeMap<u128, u128> = BTreeMap::new();
    let mut term = arena.var(x_sym);
    let mut value = x_val;
    let mut goals = Vec::with_capacity(depth);
    for _ in 0..depth {
        let out = *table
            .entry(value)
            .or_insert_with(|| rng.next_u128() & mask(width));
        term = arena.apply(f, &[term]).unwrap();
        let expected = arena.bv_const(width, out).unwrap();
        goals.push(arena.eq(term, expected).unwrap());
        value = out;
    }
    witness.set_function(f, unary_table(width, &table));

    finish(
        arena,
        goals,
        witness,
        format!("function/chain_w{width}_d{depth}_{seed:#018x}"),
        width,
        seed,
    )
}

/// Builds a satisfiable set of independent unary applications `f(x_i) = c_i`,
/// where some inputs deliberately collide so the solver's congruence
/// constraints are exercised (colliding inputs must map to the same output).
///
/// # Panics
///
/// Panics if `width` exceeds 64, if `applications` is zero, or on arena
/// corruption.
pub fn function_lookup(width: u32, applications: usize, seed: u64) -> Scenario {
    assert!(
        (1..=64).contains(&width),
        "function_lookup supports widths 1..=64"
    );
    assert!(applications >= 1, "function_lookup needs >= 1 application");
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    let f = arena
        .declare_fun("f", &[Sort::BitVec(width)], Sort::BitVec(width))
        .unwrap();

    let mut table: BTreeMap<u128, u128> = BTreeMap::new();
    let mut chosen: Vec<u128> = Vec::new();
    let mut goals = Vec::with_capacity(applications);
    for i in 0..applications {
        // With ~50% chance (after the first), reuse an earlier input value so
        // two applications share an argument and congruence must hold.
        let reuse = i > 0 && (rng.next_u128() & 1 == 0);
        let x_val = if reuse {
            let pick = usize::try_from(rng.next_u128() % chosen.len() as u128).unwrap();
            chosen[pick]
        } else {
            rng.next_u128() & mask(width)
        };
        chosen.push(x_val);
        let x_sym = arena
            .declare(&format!("x{i}"), Sort::BitVec(width))
            .unwrap();
        witness.set(x_sym, bv(width, x_val));
        let out = *table
            .entry(x_val)
            .or_insert_with(|| rng.next_u128() & mask(width));
        let x = arena.var(x_sym);
        let app = arena.apply(f, &[x]).unwrap();
        let expected = arena.bv_const(width, out).unwrap();
        goals.push(arena.eq(app, expected).unwrap());
    }
    witness.set_function(f, unary_table(width, &table));

    finish(
        arena,
        goals,
        witness,
        format!("function/lookup_w{width}_n{applications}_{seed:#018x}"),
        width,
        seed,
    )
}

/// Builds a satisfiable set of binary applications `f(a_i, b_i) = c_i` (a
/// two-argument map / merge), with deliberate argument-pair collisions to
/// exercise multi-argument congruence.
///
/// # Panics
///
/// Panics if `width` exceeds 64, if `applications` is zero, or on arena
/// corruption.
pub fn function_binary_merge(width: u32, applications: usize, seed: u64) -> Scenario {
    assert!(
        (1..=64).contains(&width),
        "function_binary_merge supports widths 1..=64"
    );
    assert!(
        applications >= 1,
        "function_binary_merge needs >= 1 application"
    );
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    let f = arena
        .declare_fun(
            "f",
            &[Sort::BitVec(width), Sort::BitVec(width)],
            Sort::BitVec(width),
        )
        .unwrap();

    let mut table: BTreeMap<(u128, u128), u128> = BTreeMap::new();
    let mut chosen: Vec<(u128, u128)> = Vec::new();
    let mut goals = Vec::with_capacity(applications);
    for i in 0..applications {
        let reuse = i > 0 && (rng.next_u128() & 1 == 0);
        let (a_val, b_val) = if reuse {
            let pick = usize::try_from(rng.next_u128() % chosen.len() as u128).unwrap();
            chosen[pick]
        } else {
            (rng.next_u128() & mask(width), rng.next_u128() & mask(width))
        };
        chosen.push((a_val, b_val));
        let a_sym = arena
            .declare(&format!("a{i}"), Sort::BitVec(width))
            .unwrap();
        let b_sym = arena
            .declare(&format!("b{i}"), Sort::BitVec(width))
            .unwrap();
        witness.set(a_sym, bv(width, a_val));
        witness.set(b_sym, bv(width, b_val));
        let out = *table
            .entry((a_val, b_val))
            .or_insert_with(|| rng.next_u128() & mask(width));
        let a = arena.var(a_sym);
        let b = arena.var(b_sym);
        let app = arena.apply(f, &[a, b]).unwrap();
        let expected = arena.bv_const(width, out).unwrap();
        goals.push(arena.eq(app, expected).unwrap());
    }
    let mut fv = FuncValue::constant(
        vec![Sort::BitVec(width), Sort::BitVec(width)],
        Sort::BitVec(width),
        0,
    );
    for (&(a, b), &out) in &table {
        fv = fv.define(&[a, b], out);
    }
    witness.set_function(f, fv);

    finish(
        arena,
        goals,
        witness,
        format!("function/merge_w{width}_n{applications}_{seed:#018x}"),
        width,
        seed,
    )
}

/// A deterministic catalog of uninterpreted-function (`QF_UFBV`) scenarios.
///
/// Kept separate from [`crate::catalog`] (pure bit-vector) and
/// [`crate::memory_catalog`] (arrays) because these require function
/// elimination to solve. Every entry is satisfiable by construction and passes
/// [`Scenario::self_check`].
pub fn function_catalog() -> Vec<Scenario> {
    let mut scenarios = Vec::new();
    for width in [4u32, 8] {
        for depth in [1usize, 3, 6] {
            scenarios.push(function_chain(
                width,
                depth,
                0xF00D_0000 ^ ((u64::from(width) << 8) | depth as u64),
            ));
        }
        for apps in [2usize, 5, 8] {
            scenarios.push(function_lookup(
                width,
                apps,
                0xFEED_0000 ^ ((u64::from(width) << 8) | apps as u64),
            ));
            scenarios.push(function_binary_merge(
                width,
                apps,
                0xCAFE_0000 ^ ((u64::from(width) << 8) | apps as u64),
            ));
        }
    }
    scenarios
}

/// Builds a `FuncValue` for a unary `BV(width) -> BV(width)` function from a
/// value table.
fn unary_table(width: u32, table: &BTreeMap<u128, u128>) -> FuncValue {
    let mut fv = FuncValue::constant(vec![Sort::BitVec(width)], Sort::BitVec(width), 0);
    for (&arg, &out) in table {
        fv = fv.define(&[arg], out);
    }
    fv
}

fn finish(
    arena: TermArena,
    goals: Vec<axeyum_ir::TermId>,
    witness: Assignment,
    name: String,
    width: u32,
    seed: u64,
) -> Scenario {
    let mut builder = Query::builder(&arena);
    for goal in goals {
        builder.assert(goal).unwrap();
    }
    let query = builder.build();
    Scenario {
        name,
        family: Family::Function,
        width,
        seed,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

fn bv(width: u32, value: u128) -> Value {
    Value::Bv { width, value }
}

#[cfg(test)]
mod tests {
    use super::{function_binary_merge, function_catalog, function_chain, function_lookup};
    use crate::{Expectation, Family};

    #[test]
    fn generators_self_check() {
        let scenarios = [
            function_chain(8, 6, 0x1234),
            function_lookup(8, 8, 0x5678),
            function_binary_merge(8, 8, 0x9abc),
        ];
        for scenario in scenarios {
            assert_eq!(scenario.family, Family::Function);
            assert!(matches!(scenario.expectation, Expectation::Sat { .. }));
            scenario
                .self_check()
                .unwrap_or_else(|error| panic!("{} failed self-check: {error}", scenario.name));
        }
    }

    #[test]
    fn catalog_is_nonempty_and_self_checks() {
        let catalog = function_catalog();
        assert!(!catalog.is_empty());
        for scenario in catalog {
            scenario
                .self_check()
                .unwrap_or_else(|error| panic!("{} failed self-check: {error}", scenario.name));
        }
    }
}
