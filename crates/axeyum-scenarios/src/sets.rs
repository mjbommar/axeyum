//! Finite-set scenarios: set algebra *is* Boolean algebra over the universe.
//!
//! Over a finite universe of `k` elements, a subset is a `BitVec(k)` bitmask and
//! the set operations are bitwise: `∩` = `&`, `∪` = `|`, complement = `~`. The
//! [set](../../../docs/curriculum/00-foundations/sets.md) laws (distributivity,
//! absorption, complement) become bit-vector identities, exhaustively checkable
//! — making concrete the lesson that set algebra and propositional logic are the
//! same Boolean lattice. Oracle-free per ADR-0008.

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, UnsatEvidence};

/// Declares a `universe`-bit subset variable.
fn subset(arena: &mut TermArena, name: &str, universe: u32) -> TermId {
    let sym = arena.declare(name, Sort::BitVec(universe)).unwrap();
    arena.var(sym)
}

/// Packages the negation of a set identity as an UNSAT scenario proven
/// exhaustively over `subset_count` subsets of a `universe`-element set.
fn unsat_set_law(
    mut arena: TermArena,
    label: String,
    universe: u32,
    subset_count: u32,
    lhs: TermId,
    rhs: TermId,
) -> Scenario {
    let equal = arena.eq(lhs, rhs).unwrap();
    let differ = arena.not(equal).unwrap();
    let mut builder = Query::builder(&arena);
    builder.assert(differ).unwrap();
    let query = builder.build();
    Scenario {
        name: label,
        family: Family::Sets,
        width: universe,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << (subset_count * universe),
            },
        },
    }
}

/// Distributivity of intersection over union: `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`
/// over a `universe`-element set — unsatisfiable negation (3 subsets).
///
/// # Panics
///
/// Panics if `3 * universe` exceeds the budget or on arena corruption.
pub fn distributivity(universe: u32) -> Scenario {
    assert!(
        3 * universe <= 20,
        "set distributivity stays inside the budget"
    );
    let mut arena = TermArena::new();
    let a = subset(&mut arena, "A", universe);
    let b = subset(&mut arena, "B", universe);
    let c = subset(&mut arena, "C", universe);
    let b_or_c = arena.bv_or(b, c).unwrap();
    let lhs = arena.bv_and(a, b_or_c).unwrap();
    let a_and_b = arena.bv_and(a, b).unwrap();
    let a_and_c = arena.bv_and(a, c).unwrap();
    let rhs = arena.bv_or(a_and_b, a_and_c).unwrap();
    unsat_set_law(
        arena,
        format!("sets/distributivity_u{universe}"),
        universe,
        3,
        lhs,
        rhs,
    )
}

/// Absorption: `A ∪ (A ∩ B) = A` over a `universe`-element set — unsatisfiable
/// negation (2 subsets).
///
/// # Panics
///
/// Panics if `2 * universe` exceeds the budget or on arena corruption.
pub fn absorption(universe: u32) -> Scenario {
    assert!(2 * universe <= 20, "set absorption stays inside the budget");
    let mut arena = TermArena::new();
    let a = subset(&mut arena, "A", universe);
    let b = subset(&mut arena, "B", universe);
    let a_and_b = arena.bv_and(a, b).unwrap();
    let lhs = arena.bv_or(a, a_and_b).unwrap();
    unsat_set_law(
        arena,
        format!("sets/absorption_u{universe}"),
        universe,
        2,
        lhs,
        a,
    )
}

/// Complement law: `A ∪ ∁A = U` (the whole universe) — unsatisfiable negation
/// (1 subset).
///
/// # Panics
///
/// Panics if `universe` exceeds the budget or on arena corruption.
pub fn complement_union_is_universe(universe: u32) -> Scenario {
    assert!(universe <= 20, "complement law stays inside the budget");
    let mut arena = TermArena::new();
    let a = subset(&mut arena, "A", universe);
    let comp = arena.bv_not(a).unwrap();
    let lhs = arena.bv_or(a, comp).unwrap();
    let universe_set = arena.bv_const(universe, crate::mask(universe)).unwrap();
    unsat_set_law(
        arena,
        format!("sets/complement_union_u{universe}"),
        universe,
        1,
        lhs,
        universe_set,
    )
}

/// A deterministic catalog of finite-set scenarios.
pub fn sets_catalog() -> Vec<Scenario> {
    vec![
        distributivity(4),
        absorption(8),
        complement_union_is_universe(8),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sets_catalog_self_checks() {
        for scenario in sets_catalog() {
            assert_eq!(scenario.family, Family::Sets);
            scenario.self_check().unwrap_or_else(|e| {
                panic!("set scenario {} failed self-check: {e}", scenario.name)
            });
        }
    }
}
