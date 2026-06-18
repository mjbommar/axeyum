//! Counting & combinatorics scenarios: the pigeonhole principle.
//!
//! The [pigeonhole principle](../../../docs/curriculum/02-structures/counting.md)
//! — `n+1` pigeons cannot occupy `n` holes without a collision — is a landmark
//! of proof complexity (Haken 1985: it has no polynomial-size resolution proof)
//! and a classic SAT/SMT benchmark. Here each pigeon's hole is a `BitVec` index
//! and "no collision" is pairwise disequality, so the unsatisfiable instances
//! self-check by exhaustive enumeration over the (small) finite domain.

use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, Value};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, UnsatEvidence};

/// Builds the "all pigeons in distinct holes" constraint over `pigeons` index
/// symbols of width `k`, returning the conjunction and the symbols.
fn distinct_assignment(arena: &mut TermArena, pigeons: usize, k: u32) -> (TermId, Vec<SymbolId>) {
    let syms: Vec<SymbolId> = (0..pigeons)
        .map(|i| arena.declare(&format!("h{i}"), Sort::BitVec(k)).unwrap())
        .collect();
    let vars: Vec<TermId> = syms.iter().map(|&s| arena.var(s)).collect();
    let mut acc: Option<TermId> = None;
    for i in 0..pigeons {
        for j in (i + 1)..pigeons {
            let eq = arena.eq(vars[i], vars[j]).unwrap();
            let ne = arena.not(eq).unwrap();
            acc = Some(match acc {
                None => ne,
                Some(prev) => arena.and(prev, ne).unwrap(),
            });
        }
    }
    // With a single pigeon there are no pairs; the constraint is trivially true.
    let constraint = acc.unwrap_or_else(|| {
        let t = arena.bv_const(1, 1).unwrap();
        arena.eq(t, t).unwrap()
    });
    (constraint, syms)
}

/// The pigeonhole principle: `holes + 1` pigeons cannot all land in distinct
/// holes. Unsatisfiable, proven exhaustively over the index domain.
///
/// `holes` must be a power of two (so every `BitVec` index is a valid hole and
/// no range guard is needed).
///
/// # Panics
///
/// Panics if `holes` is not a power of two in `2..=16`, if the domain exceeds
/// the exhaustive budget, or on arena corruption.
pub fn pigeonhole(holes: u32) -> Scenario {
    assert!(
        holes.is_power_of_two() && (2..=16).contains(&holes),
        "pigeonhole expects a power-of-two hole count in 2..=16"
    );
    let k = holes.trailing_zeros();
    let pigeons = holes + 1;
    let total_bits = pigeons * k;
    assert!(
        total_bits <= 20,
        "pigeonhole instance exceeds the exhaustive budget"
    );

    let mut arena = TermArena::new();
    let (constraint, _syms) = distinct_assignment(&mut arena, pigeons as usize, k);
    let mut builder = Query::builder(&arena);
    builder.assert(constraint).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("counting/pigeonhole_{pigeons}_into_{holes}"),
        family: Family::Counting,
        width: k,
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

/// The satisfiable counterpart: `items` pigeons into `items` holes *can* all be
/// distinct (a permutation exists). Witnessed by the identity assignment.
///
/// # Panics
///
/// Panics if `items` is not a power of two in `2..=16` or on arena corruption.
pub fn permutation_exists(items: u32) -> Scenario {
    assert!(
        items.is_power_of_two() && (2..=16).contains(&items),
        "permutation_exists expects a power-of-two item count in 2..=16"
    );
    let k = items.trailing_zeros();
    let pigeons = items as usize;

    let mut arena = TermArena::new();
    let (constraint, syms) = distinct_assignment(&mut arena, pigeons, k);
    let mut builder = Query::builder(&arena);
    builder.assert(constraint).unwrap();
    let query = builder.build();

    // The identity placement (pigeon i in hole i) is a valid permutation.
    let mut witness = Assignment::new();
    for (i, &sym) in syms.iter().enumerate() {
        witness.set(
            sym,
            Value::Bv {
                width: k,
                value: i as u128,
            },
        );
    }

    Scenario {
        name: format!("counting/permutation_{items}"),
        family: Family::Counting,
        width: k,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// A deterministic catalog of counting scenarios.
pub fn counting_catalog() -> Vec<Scenario> {
    vec![
        pigeonhole(2),
        pigeonhole(4),
        permutation_exists(4),
        permutation_exists(8),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counting_catalog_self_checks() {
        for scenario in counting_catalog() {
            assert_eq!(scenario.family, Family::Counting);
            scenario.self_check().unwrap_or_else(|e| {
                panic!("counting scenario {} failed self-check: {e}", scenario.name)
            });
        }
    }

    #[test]
    fn pigeonhole_is_exhaustively_unsat() {
        // 5 pigeons into 4 holes: 5 * 2 = 10 index bits, all enumerated.
        match pigeonhole(4).self_check().unwrap() {
            UnsatEvidence::Exhaustive { cases } => assert_eq!(cases, 1 << 10),
            sampled @ UnsatEvidence::Sampled { .. } => {
                panic!("expected exhaustive, got {sampled:?}")
            }
        }
    }
}
