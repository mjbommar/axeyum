//! Cardinality constraints (`at-most-k` / `at-least-k` / `exactly-k`), lowered
//! to a bit-vector sum.
//!
//! Z3/cvc5 expose cardinality / pseudo-Boolean constraints; this provides the
//! unweighted cardinality case, common in scheduling and combinatorial
//! optimization (the "constrained program optimization" north star). Each
//! Boolean is summed as a `0`/`1` bit-vector of width `ceil(log2(n+1))` and
//! compared with `k`. It reduces entirely to the bit-vector theory, which is
//! decided and replayed soundly — no new core machinery, and it composes with
//! the bit-vector optimizers (e.g. maximize how many of a set hold).
//!
//! Weighted pseudo-Boolean sums (`Σ wᵢ·bᵢ ⊵ k`) are the natural next extension.

use axeyum_ir::{IrError, TermArena, TermId};

/// `at-most-k`: at most `k` of `bools` are true.
///
/// # Errors
///
/// Returns [`IrError`] from the IR builders.
pub fn at_most(arena: &mut TermArena, bools: &[TermId], k: u32) -> Result<TermId, IrError> {
    let count = u32::try_from(bools.len()).unwrap_or(u32::MAX);
    if k >= count {
        // Trivially satisfiable: at most `count` can be true and k >= count.
        return Ok(arena.bool_const(true));
    }
    let (sum, width) = sum_of_bools(arena, bools)?;
    let bound = arena.bv_const(width, u128::from(k))?;
    arena.bv_ule(sum, bound)
}

/// `at-least-k`: at least `k` of `bools` are true.
///
/// # Errors
///
/// Returns [`IrError`] from the IR builders.
pub fn at_least(arena: &mut TermArena, bools: &[TermId], k: u32) -> Result<TermId, IrError> {
    let count = u32::try_from(bools.len()).unwrap_or(u32::MAX);
    if k == 0 {
        return Ok(arena.bool_const(true));
    }
    if k > count {
        // Cannot have more trues than there are Booleans.
        return Ok(arena.bool_const(false));
    }
    let (sum, width) = sum_of_bools(arena, bools)?;
    let bound = arena.bv_const(width, u128::from(k))?;
    arena.bv_uge(sum, bound)
}

/// `exactly-k`: exactly `k` of `bools` are true.
///
/// # Errors
///
/// Returns [`IrError`] from the IR builders.
pub fn exactly(arena: &mut TermArena, bools: &[TermId], k: u32) -> Result<TermId, IrError> {
    let count = u32::try_from(bools.len()).unwrap_or(u32::MAX);
    if k > count {
        return Ok(arena.bool_const(false));
    }
    let (sum, width) = sum_of_bools(arena, bools)?;
    let bound = arena.bv_const(width, u128::from(k))?;
    arena.eq(sum, bound)
}

/// `between-lo-hi`: at least `lo` and at most `hi` of `bools` are true. Equivalent
/// to `at_least(lo) ∧ at_most(hi)`; an empty range (`lo > hi`) is `false`.
///
/// # Errors
///
/// Returns [`IrError`] from the IR builders.
pub fn between(
    arena: &mut TermArena,
    bools: &[TermId],
    lo: u32,
    hi: u32,
) -> Result<TermId, IrError> {
    if lo > hi {
        return Ok(arena.bool_const(false));
    }
    let lower = at_least(arena, bools, lo)?;
    let upper = at_most(arena, bools, hi)?;
    arena.and(lower, upper)
}

/// `at-most-one`: at most one of `bools` is true (the common AMO constraint).
///
/// # Errors
///
/// Returns [`IrError`] from the IR builders.
pub fn at_most_one(arena: &mut TermArena, bools: &[TermId]) -> Result<TermId, IrError> {
    at_most(arena, bools, 1)
}

/// `exactly-one`: exactly one of `bools` is true (the common EO / one-hot
/// constraint).
///
/// # Errors
///
/// Returns [`IrError`] from the IR builders.
pub fn exactly_one(arena: &mut TermArena, bools: &[TermId]) -> Result<TermId, IrError> {
    exactly(arena, bools, 1)
}

/// Builds the bit-vector sum `Σ ite(bᵢ, 1, 0)` and returns it with its width.
/// The width is the minimal one that can hold `bools.len()`.
fn sum_of_bools(arena: &mut TermArena, bools: &[TermId]) -> Result<(TermId, u32), IrError> {
    let width = count_width(bools.len());
    let zero = arena.bv_const(width, 0)?;
    let one = arena.bv_const(width, 1)?;
    let mut sum = zero;
    for &b in bools {
        let increment = arena.ite(b, one, zero)?;
        sum = arena.bv_add(sum, increment)?;
    }
    Ok((sum, width))
}

/// The minimal bit-width that can represent the count `n` (at least 1).
fn count_width(n: usize) -> u32 {
    let n = u128::try_from(n).unwrap_or(u128::MAX);
    if n == 0 {
        return 1;
    }
    u128::BITS - n.leading_zeros()
}
