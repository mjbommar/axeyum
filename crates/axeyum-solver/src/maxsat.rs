//! `MaxSAT` / weighted-`MaxSAT`: maximize the (weighted) number of satisfied soft
//! constraints subject to the hard ones.
//!
//! Z3/cvc5 expose this as optimization over soft assertions; it is the capstone
//! of the optimization work, composing cardinality summing
//! ([`crate::at_most`] family) with the bit-vector optimizer
//! ([`crate::maximize_bv`]). Each soft constraint contributes its (unit or given)
//! weight to a bit-vector sum when satisfied; maximizing that sum subject to the
//! hard constraints is `MaxSAT`. It reduces entirely to the sound, replayed
//! bit-vector theory — no new core machinery — and returns the optimal weight
//! ([`OptOutcome::Optimal`]), [`OptOutcome::Infeasible`] when the hard
//! constraints are unsatisfiable, or [`OptOutcome::Unknown`].

use axeyum_ir::{TermArena, TermId};

use crate::backend::SolverError;
use crate::optimize::{OptOutcome, maximize_bv};

/// Maximizes how many of `soft` hold subject to all of `hard` (unweighted
/// `MaxSAT`). The optimum is the largest number of soft constraints simultaneously
/// satisfiable together with the hard constraints.
///
/// # Errors
///
/// Returns [`SolverError`] from the underlying optimizer / IR builders.
pub fn max_satisfiable(
    arena: &mut TermArena,
    hard: &[TermId],
    soft: &[TermId],
) -> Result<OptOutcome, SolverError> {
    let weighted: Vec<(TermId, u64)> = soft.iter().map(|&s| (s, 1)).collect();
    max_satisfiable_weighted(arena, hard, &weighted)
}

/// Weighted `MaxSAT`: maximizes the total weight of satisfied soft constraints
/// subject to all of `hard`. Each entry is `(soft constraint, weight)`.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if the total weight needs more than 127
/// bits, or [`SolverError`] from the optimizer / IR builders.
pub fn max_satisfiable_weighted(
    arena: &mut TermArena,
    hard: &[TermId],
    soft: &[(TermId, u64)],
) -> Result<OptOutcome, SolverError> {
    let total: u128 = soft.iter().map(|&(_, w)| u128::from(w)).sum();
    let width = weight_width(total)?;
    let zero = arena.bv_const(width, 0)?;
    let mut sum = zero;
    for &(constraint, weight) in soft {
        let value = arena.bv_const(width, u128::from(weight))?;
        let increment = arena.ite(constraint, value, zero)?;
        sum = arena.bv_add(sum, increment)?;
    }
    maximize_bv(arena, hard, sum)
}

/// The minimal bit-width to hold the total weight (at least 1, at most 127 so the
/// bit-vector optimizer accepts it).
fn weight_width(total: u128) -> Result<u32, SolverError> {
    let bits = if total == 0 {
        1
    } else {
        u128::BITS - total.leading_zeros()
    };
    if bits > 127 {
        return Err(SolverError::Unsupported(format!(
            "MaxSAT total weight needs {bits} bits, over the 127-bit optimizer limit"
        )));
    }
    Ok(bits)
}
