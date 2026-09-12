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

/// Whether `sort` mentions a datatype anywhere, including inside an array.
///
/// TERMINATION (ADR-1920). This has to be the SAME predicate the dispatcher
/// diverts on, and the two had drifted: `Features::note_sort` recurses into an
/// array's index and element sorts, so `(Array Int Color)` sets
/// `has_datatype` — while this scan tested only `Sort::Datatype(_)` on the term
/// itself, and an array-of-datatypes TERM has sort `Array`, not `Datatype`. So
/// a query with an array of datatypes and no datatype-sorted term reached the
/// fall-through `solve` below, the dispatcher diverted right back here on the
/// unchanged input, and the process died of a stack overflow.
///
/// Measured 2026-09-12 on
/// `AUFDTLIRA/20200306-Kanig/spark2014bench/P518-021__frame_for_max__…`: a
/// 22 KB file that still overflowed a **1 GiB** stack, so an unbounded cycle
/// rather than a deep term. It parses on `main` without ADR-1920, so this is a
/// live defect that predates the gate lift.
///
/// Widening this predicate is what makes the fall-through provably terminating:
/// when it says `false` for every reachable term and no `Dt*` op is present,
/// `Features::scan` over the same terms cannot set `has_datatype`, so `solve`
/// cannot route back here.
pub(crate) fn sort_mentions_datatype(sort: Sort) -> bool {
    match sort {
        Sort::Datatype(_) => true,
        Sort::Array { index, element } => {
            sort_mentions_datatype(index.to_sort()) || sort_mentions_datatype(element.to_sort())
        }
        _ => false,
    }
}

/// The first subterm that still carries datatype content (a sort mentioning a
/// datatype, or a construct/select/test op), if any.
fn first_datatype_term(arena: &TermArena, roots: &[TermId]) -> Option<TermId> {
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if sort_mentions_datatype(arena.sort_of(term)) {
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
