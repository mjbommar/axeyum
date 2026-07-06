//! Relation-and-function scenarios: finite function tables and relations as
//! packed bit-vectors.
//!
//! Exercises the
//! [relations-and-functions](../../../docs/curriculum/00-foundations/relations-and-functions.md)
//! node: a function `f : {0..3} → {0..3}` is a packed 8-bit table (entry `i`
//! is the 2-bit field at offset `2i`), and a relation on `{0,1,2}` is a 9-bit
//! adjacency mask (pair `(i, j)` is bit `3i + j`). Injectivity, composition,
//! and the equivalence-relation axioms become exhaustively checkable
//! bit-vector facts; a classic fallacy ("symmetric + transitive ⇒ reflexive")
//! is refuted by a concrete witness. Oracle-free per ADR-0008.

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, UnsatEvidence};

/// The 2-bit entry `f(i)` of a packed four-entry function table, widened to
/// the table's width.
fn table_entry(arena: &mut TermArena, table: TermId, width: u32, index: u128) -> TermId {
    let shift = arena.bv_const(width, 2 * index).unwrap();
    let shifted = arena.bv_lshr(table, shift).unwrap();
    let three = arena.bv_const(width, 3).unwrap();
    arena.bv_and(shifted, three).unwrap()
}

/// The 2-bit entry `f(x)` of a packed four-entry function table at a *term*
/// index (already reduced to `0..=3`), widened to the table's width.
fn table_apply(arena: &mut TermArena, table: TermId, width: u32, index: TermId) -> TermId {
    let shift = arena.bv_add(index, index).unwrap();
    let shifted = arena.bv_lshr(table, shift).unwrap();
    let three = arena.bv_const(width, 3).unwrap();
    arena.bv_and(shifted, three).unwrap()
}

/// The Boolean bit `r_{i,j}` of a 9-bit relation mask on `{0, 1, 2}`.
fn relation_bit(arena: &mut TermArena, relation: TermId, width: u32, i: u128, j: u128) -> TermId {
    let shift = arena.bv_const(width, 3 * i + j).unwrap();
    let shifted = arena.bv_lshr(relation, shift).unwrap();
    let one = arena.bv_const(width, 1).unwrap();
    let bit = arena.bv_and(shifted, one).unwrap();
    arena.eq(bit, one).unwrap()
}

fn conjoin(arena: &mut TermArena, terms: &[TermId]) -> TermId {
    let mut result = terms[0];
    for &term in &terms[1..] {
        result = arena.and(result, term).unwrap();
    }
    result
}

fn unsat(arena: TermArena, label: String, total_bits: u32, violation: TermId) -> Scenario {
    let mut builder = Query::builder(&arena);
    builder.assert(violation).unwrap();
    let query = builder.build();
    Scenario {
        name: label,
        family: Family::Relation,
        width: total_bits,
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

/// **Pigeonhole for functions**: no `f : {0,1,2,3} → {0,1,2}` is injective.
/// The scenario constrains every table entry into the 3-element codomain and
/// asserts pairwise distinctness; it is unsatisfiable (256 cases).
///
/// # Panics
///
/// Panics on arena corruption.
pub fn no_injection_into_smaller() -> Scenario {
    let width = 8u32;
    let mut arena = TermArena::new();
    let f_sym = arena.declare("f", Sort::BitVec(width)).unwrap();
    let f = arena.var(f_sym);
    let entries: Vec<TermId> = (0..4)
        .map(|i| table_entry(&mut arena, f, width, i))
        .collect();
    let three = arena.bv_const(width, 3).unwrap();

    let mut goals = Vec::new();
    for &entry in &entries {
        goals.push(arena.bv_ult(entry, three).unwrap());
    }
    for i in 0..4 {
        for j in (i + 1)..4 {
            let same = arena.eq(entries[i], entries[j]).unwrap();
            goals.push(arena.not(same).unwrap());
        }
    }
    let violation = conjoin(&mut arena, &goals);
    unsat(
        arena,
        "relation/no_injection_into_smaller".to_string(),
        width,
        violation,
    )
}

/// **A bijection exists** on a 4-element set: a packed table with pairwise
/// distinct entries is a permutation. Satisfiable, witnessed by the identity
/// table `0xE4` (entries `0, 1, 2, 3`).
///
/// # Panics
///
/// Panics on arena corruption.
pub fn bijection_witness() -> Scenario {
    let width = 8u32;
    let mut arena = TermArena::new();
    let f_sym = arena.declare("f", Sort::BitVec(width)).unwrap();
    let f = arena.var(f_sym);
    let entries: Vec<TermId> = (0..4)
        .map(|i| table_entry(&mut arena, f, width, i))
        .collect();

    let mut goals = Vec::new();
    for i in 0..4 {
        for j in (i + 1)..4 {
            let same = arena.eq(entries[i], entries[j]).unwrap();
            goals.push(arena.not(same).unwrap());
        }
    }
    let all = conjoin(&mut arena, &goals);

    let mut builder = Query::builder(&arena);
    builder.assert(all).unwrap();
    let query = builder.build();

    let mut witness = Assignment::new();
    witness.set(f_sym, Value::Bv { width, value: 0xE4 });

    Scenario {
        name: "relation/bijection_witness".to_string(),
        family: Family::Relation,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// **The classic fallacy refuted**: "symmetric + transitive ⇒ reflexive" is
/// false — the empty relation on `{0, 1, 2}` is symmetric and transitive but
/// not reflexive. The scenario asserts symmetry, transitivity, and the failure
/// of reflexivity; it is satisfiable with the empty-relation witness.
///
/// # Panics
///
/// Panics on arena corruption.
pub fn symmetric_transitive_not_reflexive() -> Scenario {
    let width = 9u32;
    let mut arena = TermArena::new();
    let r_sym = arena.declare("r", Sort::BitVec(width)).unwrap();
    let r = arena.var(r_sym);

    let mut goals = Vec::new();
    // Symmetry: r_{i,j} ↔ r_{j,i}.
    for i in 0..3 {
        for j in (i + 1)..3 {
            let forward = relation_bit(&mut arena, r, width, i, j);
            let backward = relation_bit(&mut arena, r, width, j, i);
            goals.push(arena.eq(forward, backward).unwrap());
        }
    }
    // Transitivity: r_{i,j} ∧ r_{j,k} ⇒ r_{i,k}.
    for i in 0..3 {
        for j in 0..3 {
            for k in 0..3 {
                let ij = relation_bit(&mut arena, r, width, i, j);
                let jk = relation_bit(&mut arena, r, width, j, k);
                let ik = relation_bit(&mut arena, r, width, i, k);
                let both = arena.and(ij, jk).unwrap();
                goals.push(arena.implies(both, ik).unwrap());
            }
        }
    }
    // Not reflexive: some diagonal bit is off.
    let d0 = relation_bit(&mut arena, r, width, 0, 0);
    let d1 = relation_bit(&mut arena, r, width, 1, 1);
    let d2 = relation_bit(&mut arena, r, width, 2, 2);
    let d01 = arena.and(d0, d1).unwrap();
    let diagonal = arena.and(d01, d2).unwrap();
    goals.push(arena.not(diagonal).unwrap());

    let all = conjoin(&mut arena, &goals);
    let mut builder = Query::builder(&arena);
    builder.assert(all).unwrap();
    let query = builder.build();

    let mut witness = Assignment::new();
    witness.set(r_sym, Value::Bv { width, value: 0 });

    Scenario {
        name: "relation/symmetric_transitive_not_reflexive".to_string(),
        family: Family::Relation,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// **Composition preserves injectivity**: if `f` and `g` on `{0, 1, 2}` are
/// injective, so is `g ∘ f`. Each table packs three 2-bit entries constrained
/// into the domain; the scenario asserts both tables injective and the
/// composite not injective, and is unsatisfiable (4096 cases).
///
/// # Panics
///
/// Panics on arena corruption.
pub fn injective_composition() -> Scenario {
    let width = 6u32;
    let mut arena = TermArena::new();
    let f_sym = arena.declare("f", Sort::BitVec(width)).unwrap();
    let g_sym = arena.declare("g", Sort::BitVec(width)).unwrap();
    let f = arena.var(f_sym);
    let g = arena.var(g_sym);

    let f_entries: Vec<TermId> = (0..3)
        .map(|i| table_entry(&mut arena, f, width, i))
        .collect();
    let g_entries: Vec<TermId> = (0..3)
        .map(|i| table_entry(&mut arena, g, width, i))
        .collect();
    let composed: Vec<TermId> = f_entries
        .iter()
        .map(|&fi| table_apply(&mut arena, g, width, fi))
        .collect();

    let mut goals = Vec::new();
    let three = arena.bv_const(width, 3).unwrap();
    for entries in [&f_entries, &g_entries] {
        for &entry in entries {
            goals.push(arena.bv_ult(entry, three).unwrap());
        }
        for i in 0..3 {
            for j in (i + 1)..3 {
                let same = arena.eq(entries[i], entries[j]).unwrap();
                goals.push(arena.not(same).unwrap());
            }
        }
    }
    // The composite collides somewhere.
    let mut collisions = Vec::new();
    for i in 0..3 {
        for j in (i + 1)..3 {
            collisions.push(arena.eq(composed[i], composed[j]).unwrap());
        }
    }
    let mut some_collision = collisions[0];
    for &collision in &collisions[1..] {
        some_collision = arena.or(some_collision, collision).unwrap();
    }
    goals.push(some_collision);

    let violation = conjoin(&mut arena, &goals);
    unsat(
        arena,
        "relation/injective_composition".to_string(),
        12,
        violation,
    )
}

/// A deterministic catalog of relation-and-function scenarios.
pub fn relation_catalog() -> Vec<Scenario> {
    vec![
        no_injection_into_smaller(),
        bijection_witness(),
        symmetric_transitive_not_reflexive(),
        injective_composition(),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn relation_catalog_self_checks() {
        for scenario in relation_catalog() {
            assert_eq!(scenario.family, Family::Relation);
            scenario.self_check().unwrap_or_else(|e| {
                panic!("relation scenario {} failed self-check: {e}", scenario.name)
            });
        }
    }

    #[test]
    fn empty_relation_refutes_the_fallacy() {
        let scenario = symmetric_transitive_not_reflexive();
        assert!(matches!(scenario.expectation, Expectation::Sat { .. }));
        scenario.self_check().unwrap();
    }
}
