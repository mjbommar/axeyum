//! Software-verification scenarios: the "Hello, World" of program safety.
//!
//! Small, classic verification tasks over machine integers (`BitVec`): some are
//! **safety theorems** (the negation is unsatisfiable — proven exhaustively),
//! others are **bugs** with a concrete counterexample (satisfiable — witnessed
//! and replay-checked). They teach the canonical pitfalls of fixed-width
//! arithmetic (the `INT_MIN` abs overflow; the Bloch binary-search midpoint
//! overflow) while exercising axeyum's signed/unsigned BV operators end to end.
//!
//! These map to the solver-capability concept [`crate::Concept::SoftwareVerification`]
//! and are oracle-free per ADR-0008.

use axeyum_ir::{Assignment, Sort, TermArena, Value};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, UnsatEvidence, mask};

/// `abs` is **not** always non-negative: at `INT_MIN`, two's-complement negation
/// overflows (`−INT_MIN = INT_MIN`), so `abs(INT_MIN) < 0`. Satisfiable, with
/// `x = INT_MIN` as the counterexample witness.
///
/// # Panics
///
/// Panics if `width` is outside `2..=32` or on arena corruption.
pub fn abs_non_negative_bug(width: u32) -> Scenario {
    assert!((2..=32).contains(&width), "abs bug needs width 2..=32");
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.bv_const(width, 0).unwrap();
    let neg_x = arena.bv_neg(x).unwrap();
    let is_neg = arena.bv_slt(x, zero).unwrap();
    let abs = arena.ite(is_neg, neg_x, x).unwrap();
    // The (false) safety claim is `abs >= 0`; assert its violation.
    let abs_negative = arena.bv_slt(abs, zero).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(abs_negative).unwrap();
    let query = builder.build();

    let int_min = 1u128 << (width - 1);
    let mut witness = Assignment::new();
    witness.set(
        x_sym,
        Value::Bv {
            width,
            value: int_min,
        },
    );

    Scenario {
        name: format!("verification/abs_non_negative_bug_w{width}"),
        family: Family::Verification,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// Safety theorem: `max(a, b) ≥ a ∧ max(a, b) ≥ b` (signed). The negation is
/// unsatisfiable, proven exhaustively (2 symbols).
///
/// # Panics
///
/// Panics if `2 * width` exceeds the budget or on arena corruption.
pub fn max_is_an_upper_bound(width: u32) -> Scenario {
    assert!(2 * width <= 20, "max theorem stays inside the budget");
    let mut arena = TermArena::new();
    let a = arena
        .declare("a", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let b = arena
        .declare("b", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let a_ge_b = arena.bv_sge(a, b).unwrap();
    let max = arena.ite(a_ge_b, a, b).unwrap();
    let lt_a = arena.bv_slt(max, a).unwrap();
    let lt_b = arena.bv_slt(max, b).unwrap();
    // Negation of the theorem: max is below one of its arguments.
    let bad = arena.or(lt_a, lt_b).unwrap();
    unsat_exhaustive(
        arena,
        format!("verification/max_upper_bound_w{width}"),
        width,
        2,
        bad,
    )
}

/// Safety theorem: the unsigned **overflow-detection idiom** is correct —
/// `(a + b) <ᵤ a` (the carry test) iff `b >ᵤ ¬a`. The negation is
/// unsatisfiable, proven exhaustively (2 symbols).
///
/// # Panics
///
/// Panics if `2 * width` exceeds the budget or on arena corruption.
pub fn unsigned_overflow_idiom(width: u32) -> Scenario {
    assert!(2 * width <= 20, "overflow idiom stays inside the budget");
    let mut arena = TermArena::new();
    let a = arena
        .declare("a", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let b = arena
        .declare("b", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let sum = arena.bv_add(a, b).unwrap();
    let carry_test = arena.bv_ult(sum, a).unwrap();
    let not_a = arena.bv_not(a).unwrap();
    let bound_test = arena.bv_ugt(b, not_a).unwrap();
    let agree = arena.eq(carry_test, bound_test).unwrap();
    let bad = arena.not(agree).unwrap();
    unsat_exhaustive(
        arena,
        format!("verification/unsigned_overflow_idiom_w{width}"),
        width,
        2,
        bad,
    )
}

/// Safety theorem: a **saturating add** never drops below its first operand:
/// `satadd(a, b) ≥ᵤ a`. The negation is unsatisfiable, proven exhaustively.
///
/// # Panics
///
/// Panics if `2 * width` exceeds the budget or on arena corruption.
pub fn saturating_add_safe(width: u32) -> Scenario {
    assert!(2 * width <= 20, "saturating add stays inside the budget");
    let mut arena = TermArena::new();
    let a = arena
        .declare("a", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let b = arena
        .declare("b", Sort::BitVec(width))
        .map(|s| arena.var(s))
        .unwrap();
    let sum = arena.bv_add(a, b).unwrap();
    let overflow = arena.bv_ult(sum, a).unwrap();
    let all_ones = arena.bv_const(width, mask(width)).unwrap();
    let satadd = arena.ite(overflow, all_ones, sum).unwrap();
    let below = arena.bv_ult(satadd, a).unwrap();
    unsat_exhaustive(
        arena,
        format!("verification/saturating_add_safe_w{width}"),
        width,
        2,
        below,
    )
}

/// The **Bloch binary-search midpoint bug**: `(lo + hi) / 2` overflows for large
/// `lo, hi`, so it differs from the safe `lo + (hi − lo) / 2`. Satisfiable under
/// `0 ≤ lo ≤ hi`, witnessed by `lo = hi = 2^(width−2)` (where `lo + hi` overflows
/// into the negatives).
///
/// # Panics
///
/// Panics if `width` is outside `4..=32` or on arena corruption.
pub fn midpoint_overflow_bug(width: u32) -> Scenario {
    assert!((4..=32).contains(&width), "midpoint bug needs width 4..=32");
    let mut arena = TermArena::new();
    let lo_sym = arena.declare("lo", Sort::BitVec(width)).unwrap();
    let hi_sym = arena.declare("hi", Sort::BitVec(width)).unwrap();
    let lo = arena.var(lo_sym);
    let hi = arena.var(hi_sym);
    let zero = arena.bv_const(width, 0).unwrap();
    let two = arena.bv_const(width, 2).unwrap();
    let lo_nonneg = arena.bv_sle(zero, lo).unwrap();
    let lo_le_hi = arena.bv_sle(lo, hi).unwrap();
    let pre = arena.and(lo_nonneg, lo_le_hi).unwrap();
    // Naive midpoint vs. the safe one.
    let sum = arena.bv_add(lo, hi).unwrap();
    let naive = arena.bv_sdiv(sum, two).unwrap();
    let span = arena.bv_sub(hi, lo).unwrap();
    let half_span = arena.bv_sdiv(span, two).unwrap();
    let safe_mid = arena.bv_add(lo, half_span).unwrap();
    let equal = arena.eq(naive, safe_mid).unwrap();
    let differ = arena.not(equal).unwrap();
    let goal = arena.and(pre, differ).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(goal).unwrap();
    let query = builder.build();

    let value = 1u128 << (width - 2);
    let mut witness = Assignment::new();
    witness.set(lo_sym, Value::Bv { width, value });
    witness.set(hi_sym, Value::Bv { width, value });

    Scenario {
        name: format!("verification/midpoint_overflow_bug_w{width}"),
        family: Family::Verification,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// Packages a Boolean `bad` term (the negation of a safety theorem) as an UNSAT
/// scenario proven exhaustively over `symbol_count` `width`-bit symbols.
fn unsat_exhaustive(
    arena: TermArena,
    label: String,
    width: u32,
    symbol_count: u32,
    bad: axeyum_ir::TermId,
) -> Scenario {
    let mut builder = Query::builder(&arena);
    builder.assert(bad).unwrap();
    let query = builder.build();
    Scenario {
        name: label,
        family: Family::Verification,
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

/// A deterministic catalog of software-verification scenarios.
pub fn verification_catalog() -> Vec<Scenario> {
    vec![
        abs_non_negative_bug(8),
        max_is_an_upper_bound(8),
        unsigned_overflow_idiom(8),
        saturating_add_safe(8),
        midpoint_overflow_bug(8),
        midpoint_overflow_bug(16),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verification_catalog_self_checks() {
        for scenario in verification_catalog() {
            assert_eq!(scenario.family, Family::Verification);
            scenario.self_check().unwrap_or_else(|e| {
                panic!(
                    "verification scenario {} failed self-check: {e}",
                    scenario.name
                )
            });
        }
    }

    #[test]
    fn abs_bug_witness_is_int_min() {
        let scenario = abs_non_negative_bug(8);
        assert!(matches!(scenario.expectation, Expectation::Sat { .. }));
        // The INT_MIN witness genuinely makes abs negative.
        scenario.self_check().unwrap();
    }

    #[test]
    fn midpoint_bug_is_a_real_counterexample() {
        let scenario = midpoint_overflow_bug(8);
        assert!(matches!(scenario.expectation, Expectation::Sat { .. }));
        scenario.self_check().unwrap();
    }
}
