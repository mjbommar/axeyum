//! The `distinct` (all-different) constraint.
//!
//! `distinct` is an SMT-LIB / Z3 builtin asserting its arguments are pairwise
//! unequal — the backbone of all-different modeling (graph coloring, scheduling,
//! Latin squares). It expands to the conjunction of pairwise disequalities, so it
//! works for any sort the equality builder accepts and inherits that theory's
//! soundness with no new machinery.

use axeyum_ir::{IrError, TermArena, TermId};

/// Builds `distinct(terms)`: every pair of `terms` is unequal. Fewer than two
/// terms is vacuously `true`.
///
/// # Errors
///
/// Returns [`IrError`] from the equality/Boolean builders (e.g. a sort mismatch
/// between two terms).
pub fn distinct(arena: &mut TermArena, terms: &[TermId]) -> Result<TermId, IrError> {
    let mut conjunction: Option<TermId> = None;
    for i in 0..terms.len() {
        for j in (i + 1)..terms.len() {
            let equal = arena.eq(terms[i], terms[j])?;
            let unequal = arena.not(equal)?;
            conjunction = Some(match conjunction {
                None => unequal,
                Some(acc) => arena.and(acc, unequal)?,
            });
        }
    }
    Ok(conjunction.unwrap_or_else(|| arena.bool_const(true)))
}
