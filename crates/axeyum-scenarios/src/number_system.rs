//! Number-system scenarios: order and successor structure over bit-vectors.
//!
//! Exercises the [integers](../../../docs/curriculum/01-number-systems/integers.md)
//! (signed order: trichotomy, transitivity) and
//! [naturals](../../../docs/curriculum/01-number-systems/naturals.md) (unsigned
//! non-negativity, successor injectivity) nodes — the order axioms and a Peano
//! property as exhaustively checkable bit-vector theorems. Oracle-free per
//! ADR-0008.

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, UnsatEvidence};

fn var(arena: &mut TermArena, name: &str, width: u32) -> TermId {
    let sym = arena.declare(name, Sort::BitVec(width)).unwrap();
    arena.var(sym)
}

/// Packages a Boolean `violation` term (the negation of a theorem) as an UNSAT
/// scenario proven exhaustively over `symbol_count` `width`-bit symbols.
fn unsat(
    arena: TermArena,
    label: String,
    width: u32,
    symbol_count: u32,
    violation: TermId,
) -> Scenario {
    let mut builder = Query::builder(&arena);
    builder.assert(violation).unwrap();
    let query = builder.build();
    Scenario {
        name: label,
        family: Family::NumberSystem,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive {
                cases: 1u64 << (symbol_count * width),
            },
        },
    }
}

/// Signed-order **trichotomy**: for all `a, b`, exactly one of `a < b`, `a = b`,
/// `a > b` holds. The negation is unsatisfiable, proven exhaustively (2 symbols).
///
/// # Panics
///
/// Panics if `2 * width` exceeds the budget or on arena corruption.
pub fn signed_trichotomy(width: u32) -> Scenario {
    assert!(2 * width <= 20, "trichotomy stays inside the budget");
    let mut arena = TermArena::new();
    let a = var(&mut arena, "a", width);
    let b = var(&mut arena, "b", width);
    let lt = arena.bv_slt(a, b).unwrap();
    let eq = arena.eq(a, b).unwrap();
    let gt = arena.bv_sgt(a, b).unwrap();
    let lt_or_eq = arena.or(lt, eq).unwrap();
    let some = arena.or(lt_or_eq, gt).unwrap();
    let lt_and_eq = arena.and(lt, eq).unwrap();
    let lt_and_gt = arena.and(lt, gt).unwrap();
    let eq_and_gt = arena.and(eq, gt).unwrap();
    let no_lt_eq = arena.not(lt_and_eq).unwrap();
    let no_lt_gt = arena.not(lt_and_gt).unwrap();
    let no_eq_gt = arena.not(eq_and_gt).unwrap();
    let pairwise = arena.and(no_lt_eq, no_lt_gt).unwrap();
    let mutually_exclusive = arena.and(pairwise, no_eq_gt).unwrap();
    let exactly_one = arena.and(some, mutually_exclusive).unwrap();
    let violation = arena.not(exactly_one).unwrap();
    unsat(
        arena,
        format!("number_system/signed_trichotomy_w{width}"),
        width,
        2,
        violation,
    )
}

/// Signed-order **transitivity**: `a < b ∧ b < c ⇒ a < c`. The negation is
/// unsatisfiable, proven exhaustively (3 symbols).
///
/// # Panics
///
/// Panics if `3 * width` exceeds the budget or on arena corruption.
pub fn order_transitivity(width: u32) -> Scenario {
    assert!(3 * width <= 20, "transitivity stays inside the budget");
    let mut arena = TermArena::new();
    let a = var(&mut arena, "a", width);
    let b = var(&mut arena, "b", width);
    let c = var(&mut arena, "c", width);
    let a_lt_b = arena.bv_slt(a, b).unwrap();
    let b_lt_c = arena.bv_slt(b, c).unwrap();
    let a_lt_c = arena.bv_slt(a, c).unwrap();
    let hyp = arena.and(a_lt_b, b_lt_c).unwrap();
    let not_concl = arena.not(a_lt_c).unwrap();
    let violation = arena.and(hyp, not_concl).unwrap();
    unsat(
        arena,
        format!("number_system/order_transitivity_w{width}"),
        width,
        3,
        violation,
    )
}

/// **Naturals are non-negative**: every unsigned value satisfies `x ≥ᵤ 0`. The
/// negation (`x <ᵤ 0`) is unsatisfiable, proven exhaustively (1 symbol).
///
/// # Panics
///
/// Panics if `width` exceeds the budget or on arena corruption.
pub fn unsigned_non_negative(width: u32) -> Scenario {
    assert!(width <= 20, "non-negativity stays inside the budget");
    let mut arena = TermArena::new();
    let x = var(&mut arena, "x", width);
    let zero = arena.bv_const(width, 0).unwrap();
    let below_zero = arena.bv_ult(x, zero).unwrap();
    unsat(
        arena,
        format!("number_system/unsigned_non_negative_w{width}"),
        width,
        1,
        below_zero,
    )
}

/// Peano **successor injectivity**: `x + 1 = y + 1 ⇒ x = y`. The negation is
/// unsatisfiable, proven exhaustively (2 symbols).
///
/// # Panics
///
/// Panics if `2 * width` exceeds the budget or on arena corruption.
pub fn successor_injective(width: u32) -> Scenario {
    assert!(
        2 * width <= 20,
        "successor injectivity stays inside the budget"
    );
    let mut arena = TermArena::new();
    let x = var(&mut arena, "x", width);
    let y = var(&mut arena, "y", width);
    let one = arena.bv_const(width, 1).unwrap();
    let sx = arena.bv_add(x, one).unwrap();
    let sy = arena.bv_add(y, one).unwrap();
    let succ_eq = arena.eq(sx, sy).unwrap();
    let x_eq_y = arena.eq(x, y).unwrap();
    let not_eq = arena.not(x_eq_y).unwrap();
    let violation = arena.and(succ_eq, not_eq).unwrap();
    unsat(
        arena,
        format!("number_system/successor_injective_w{width}"),
        width,
        2,
        violation,
    )
}

/// A deterministic catalog of number-system scenarios.
pub fn number_system_catalog() -> Vec<Scenario> {
    vec![
        signed_trichotomy(8),
        order_transitivity(6),
        unsigned_non_negative(16),
        successor_injective(8),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn number_system_catalog_self_checks() {
        for scenario in number_system_catalog() {
            assert_eq!(scenario.family, Family::NumberSystem);
            scenario.self_check().unwrap_or_else(|e| {
                panic!(
                    "number-system scenario {} failed self-check: {e}",
                    scenario.name
                )
            });
        }
    }
}
