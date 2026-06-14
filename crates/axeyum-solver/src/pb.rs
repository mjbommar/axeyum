//! Weighted pseudo-Boolean (PB) constraints, lowered to a bit-vector sum.
//!
//! Z3/cvc5 expose pseudo-Boolean constraints `Σ wᵢ·bᵢ ⊵ k` over Booleans; this
//! builds them as a Boolean term by summing each weight into a bit-vector when
//! its literal holds and comparing with `k`. It generalizes the unweighted
//! [`crate::at_most`] family and is the constraint counterpart of weighted
//! [`crate::max_satisfiable_weighted`] (which *optimizes* the same sum). Everything
//! reduces to the sound, replayed bit-vector theory — no new core machinery.

use axeyum_ir::{IrError, TermArena, TermId};

/// `Σ wᵢ·bᵢ <= k` over the `(literal, weight)` pairs `terms`.
///
/// # Errors
///
/// Returns [`IrError`] from the IR builders.
pub fn pb_le(arena: &mut TermArena, terms: &[(TermId, u64)], k: u64) -> Result<TermId, IrError> {
    let total: u128 = terms.iter().map(|&(_, w)| u128::from(w)).sum();
    if u128::from(k) >= total {
        return Ok(arena.bool_const(true));
    }
    let (sum, width) = weighted_sum(arena, terms, k)?;
    let bound = arena.bv_const(width, u128::from(k))?;
    arena.bv_ule(sum, bound)
}

/// `Σ wᵢ·bᵢ >= k` over the `(literal, weight)` pairs `terms`.
///
/// # Errors
///
/// Returns [`IrError`] from the IR builders.
pub fn pb_ge(arena: &mut TermArena, terms: &[(TermId, u64)], k: u64) -> Result<TermId, IrError> {
    let total: u128 = terms.iter().map(|&(_, w)| u128::from(w)).sum();
    if k == 0 {
        return Ok(arena.bool_const(true));
    }
    if u128::from(k) > total {
        return Ok(arena.bool_const(false));
    }
    let (sum, width) = weighted_sum(arena, terms, k)?;
    let bound = arena.bv_const(width, u128::from(k))?;
    arena.bv_uge(sum, bound)
}

/// `Σ wᵢ·bᵢ == k` over the `(literal, weight)` pairs `terms`.
///
/// # Errors
///
/// Returns [`IrError`] from the IR builders.
pub fn pb_eq(arena: &mut TermArena, terms: &[(TermId, u64)], k: u64) -> Result<TermId, IrError> {
    let total: u128 = terms.iter().map(|&(_, w)| u128::from(w)).sum();
    if u128::from(k) > total {
        return Ok(arena.bool_const(false));
    }
    let (sum, width) = weighted_sum(arena, terms, k)?;
    let bound = arena.bv_const(width, u128::from(k))?;
    arena.eq(sum, bound)
}

/// Builds `Σ ite(bᵢ, wᵢ, 0)` as a bit-vector wide enough to hold both the total
/// weight and the bound `k`, returning it with its width.
fn weighted_sum(
    arena: &mut TermArena,
    terms: &[(TermId, u64)],
    k: u64,
) -> Result<(TermId, u32), IrError> {
    let total: u128 = terms.iter().map(|&(_, w)| u128::from(w)).sum();
    let width = value_width(total.max(u128::from(k)));
    let zero = arena.bv_const(width, 0)?;
    let mut sum = zero;
    for &(literal, weight) in terms {
        let value = arena.bv_const(width, u128::from(weight))?;
        let increment = arena.ite(literal, value, zero)?;
        sum = arena.bv_add(sum, increment)?;
    }
    Ok((sum, width))
}

/// The minimal bit-width to represent `value` (at least 1).
fn value_width(value: u128) -> u32 {
    if value == 0 {
        1
    } else {
        u128::BITS - value.leading_zeros()
    }
}
