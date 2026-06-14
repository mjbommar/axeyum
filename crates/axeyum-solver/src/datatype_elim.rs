//! Datatype solving by read-over-construct elimination (ADR-0022).
//!
//! The first datatype *solving* slice, built on the denotation-preserving
//! [`simplify_datatypes`] rewrite: fold `select`/`test` over explicit
//! constructors, then — if no datatype sort or operator remains — decide the
//! residual query with the normal dispatcher. This handles datatype terms that
//! are *built from constructors* (the read-over-construct fragment, analogous to
//! the first array-elimination slice). Queries that still mention datatype
//! variables after simplification need a native datatype theory (eager bounded
//! unfolding, then acyclicity+congruence — ADR-0022) and are reported
//! `Unsupported`.
//!
//! Soundness: simplification preserves denotation and adds no symbols, so a
//! model of the residual query is a model of the original; the dispatcher
//! replays it, so `sat` is sound, and `unsat` of an equivalent query transfers.

use std::collections::BTreeSet;

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};
use axeyum_rewrite::simplify_datatypes;

use crate::auto::solve;
use crate::backend::{CheckResult, SolverConfig, SolverError};

/// Decides a query containing datatypes by read-over-construct elimination.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if datatype content remains after
/// simplification (a native datatype theory is needed), or [`SolverError`] from
/// the rewrite or the dispatcher.
pub fn check_with_datatype_elimination(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let simplified =
        simplify_datatypes(arena, assertions).map_err(|e| SolverError::Backend(e.to_string()))?;
    if first_datatype_term(arena, &simplified).is_some() {
        // Free datatype variables remain: hand the residual to the native
        // tag/field expansion (ADR-0022 step B), which decides the
        // non-recursive scalar-field fragment and projects datatype models.
        return crate::datatype_native::check_with_datatype_native(arena, &simplified, config);
    }
    solve(arena, &simplified, config)
}

/// The first subterm that still carries datatype content (a datatype sort or a
/// construct/select/test op), if any.
fn first_datatype_term(arena: &TermArena, roots: &[TermId]) -> Option<TermId> {
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if matches!(arena.sort_of(term), Sort::Datatype(_)) {
            return Some(term);
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(
                op,
                Op::DtConstruct { .. } | Op::DtSelect { .. } | Op::DtTest(_)
            ) {
                return Some(term);
            }
            stack.extend(args.iter().copied());
        }
    }
    None
}
