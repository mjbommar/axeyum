//! Opt-in, clock-free term-size diagnostics for the rewrite passes every
//! query pays before a theory solver ever sees the result: canonicalization,
//! [`crate::eliminate_arrays`], [`crate::eliminate_functions`],
//! [`crate::eliminate_int_divmod`], and [`crate::blast_integers`].
//!
//! Each of those passes already returns a result type richer than a bare
//! `Vec<TermId>` (ADR-1721 / ADR-1730) with its own eliminated-construct and
//! added-constraint counts (`ArrayElimination::selects`,
//! `FunctionElimination::applications`, `IntDivModElimination::replacements`
//! / `added_constraints`, `IntBlasting::restricting_constraints`), so this
//! module does not duplicate any of that. What none of them reports is the
//! shared term-size footprint before and after — the number a caller needs
//! to answer "did this pass shrink, grow, or blow up the shared DAG", which
//! is exactly [`axeyum_ir::TermStats`]. This module adds a `_with_stats`
//! wrapper per pass that calls [`TermStats::compute`] once on the input
//! roots and once on the output roots, **only when the caller opts into the
//! wrapper**.
//!
//! Opt-in here means "a separate function", not a runtime flag: the
//! unwrapped entry points (`canonicalize_terms`, `eliminate_arrays`, …) are
//! completely untouched by this module, so every existing caller pays
//! exactly what it always paid — asserted by
//! `tests::wrapped_and_unwrapped_agree_on_every_pass`, which runs each pass
//! both ways over the same input and requires byte-identical output.

use axeyum_ir::{TermArena, TermId, TermStats};

use crate::RewriteRuleId;
use crate::arrays::{ArrayElimError, ArrayElimination};
use crate::canonical::{CanonicalizeTermsOutcome, RewriteError, RewriteReport};
use crate::functions::{FuncElimError, FunctionElimination};
use crate::int_blast::{IntBlastError, IntBlasting};
use crate::int_divmod::IntDivModElimination;
use axeyum_ir::IrError;

/// Term-size footprint of one side (before or after) of a rewrite pass — a
/// projection of [`TermStats`] onto the fields a preprocessing-cost
/// diagnosis needs.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct PassSize {
    /// Unique DAG nodes reachable from the pass's root terms.
    pub dag_nodes: u64,
    /// Nodes of the fully unfolded tree, saturating at `u64::MAX` — the
    /// representational-blowup signal (see [`TermStats`]'s doc comment).
    pub tree_nodes: u64,
    /// Longest root-to-leaf path.
    pub max_depth: u64,
}

impl From<TermStats> for PassSize {
    fn from(stats: TermStats) -> Self {
        Self {
            dag_nodes: stats.dag_nodes,
            tree_nodes: stats.tree_nodes,
            max_depth: stats.max_depth,
        }
    }
}

impl PassSize {
    /// Computes the footprint of `roots` in `arena`. `O(|roots| DAG)`, memoized
    /// — the same cost `TermStats::compute` always has; call only when you
    /// intend to look at the result.
    #[must_use]
    pub fn of(arena: &TermArena, roots: &[TermId]) -> Self {
        TermStats::compute(arena, roots).into()
    }
}

/// Term-size before and after one rewrite pass.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PassSizeDelta {
    /// Footprint of the pass's input assertions.
    pub before: PassSize,
    /// Footprint of the pass's output assertions.
    pub after: PassSize,
}

impl PassSizeDelta {
    /// `after.dag_nodes - before.dag_nodes` as a signed delta. Positive is the
    /// common case (every elimination pass here adds fresh symbols and
    /// defining constraints); negative means the pass net-shrank the shared
    /// DAG.
    #[must_use]
    pub fn dag_node_delta(&self) -> i64 {
        i64::try_from(self.after.dag_nodes).unwrap_or(i64::MAX)
            - i64::try_from(self.before.dag_nodes).unwrap_or(i64::MAX)
    }
}

/// Per-rule application counts from a [`RewriteReport`], in deterministic
/// (rule-id-sorted, not discovery) order — a `BTreeMap` summary of
/// [`RewriteReport::applications`], which already carries the full
/// discovery-order log this derives from.
#[must_use]
pub fn rule_application_counts(report: &RewriteReport) -> Vec<(RewriteRuleId, u64)> {
    let mut counts: std::collections::BTreeMap<RewriteRuleId, u64> =
        std::collections::BTreeMap::new();
    for application in report.applications() {
        *counts.entry(application.rule_id.clone()).or_insert(0) += 1;
    }
    counts.into_iter().collect()
}

/// [`crate::canonicalize_terms`], additionally reporting the term-size
/// footprint before and after.
///
/// # Errors
///
/// Returns whatever [`crate::canonicalize_terms`] returns.
pub fn canonicalize_terms_with_stats(
    arena: &mut TermArena,
    roots: &[TermId],
) -> Result<(CanonicalizeTermsOutcome, PassSizeDelta), RewriteError> {
    let before = PassSize::of(arena, roots);
    let outcome = crate::canonical::canonicalize_terms(arena, roots)?;
    let after = PassSize::of(arena, &outcome.terms);
    Ok((outcome, PassSizeDelta { before, after }))
}

/// [`crate::eliminate_arrays`], additionally reporting the term-size
/// footprint before and after.
///
/// # Errors
///
/// Returns whatever [`crate::eliminate_arrays`] returns.
pub fn eliminate_arrays_with_stats(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<(ArrayElimination, PassSizeDelta), ArrayElimError> {
    let before = PassSize::of(arena, assertions);
    let elimination = crate::arrays::eliminate_arrays(arena, assertions)?;
    let after = PassSize::of(arena, elimination.assertions());
    Ok((elimination, PassSizeDelta { before, after }))
}

/// [`crate::eliminate_functions`], additionally reporting the term-size
/// footprint before and after.
///
/// # Errors
///
/// Returns whatever [`crate::eliminate_functions`] returns.
pub fn eliminate_functions_with_stats(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<(FunctionElimination, PassSizeDelta), FuncElimError> {
    let before = PassSize::of(arena, assertions);
    let elimination = crate::functions::eliminate_functions(arena, assertions)?;
    let after = PassSize::of(arena, elimination.assertions());
    Ok((elimination, PassSizeDelta { before, after }))
}

/// [`crate::eliminate_int_divmod`], additionally reporting the term-size
/// footprint before and after.
///
/// # Errors
///
/// Returns whatever [`crate::eliminate_int_divmod`] returns.
pub fn eliminate_int_divmod_with_stats(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<(IntDivModElimination, PassSizeDelta), IrError> {
    let before = PassSize::of(arena, assertions);
    let elimination = crate::int_divmod::eliminate_int_divmod(arena, assertions)?;
    let after = PassSize::of(arena, elimination.assertions());
    Ok((elimination, PassSizeDelta { before, after }))
}

/// [`crate::blast_integers`], additionally reporting the term-size footprint
/// before and after.
///
/// # Errors
///
/// Returns whatever [`crate::blast_integers`] returns.
pub fn blast_integers_with_stats(
    arena: &mut TermArena,
    assertions: &[TermId],
    width: u32,
) -> Result<(IntBlasting, PassSizeDelta), IntBlastError> {
    let before = PassSize::of(arena, assertions);
    let blasting = crate::int_blast::blast_integers(arena, assertions, width)?;
    let after = PassSize::of(arena, blasting.assertions());
    Ok((blasting, PassSizeDelta { before, after }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::TermArena;

    #[test]
    fn canonicalize_with_stats_matches_unwrapped_and_reports_growth_or_shrinkage() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let reflexive = arena.eq(x, x).unwrap();

        let mut arena_unwrapped = arena.clone();
        let direct = crate::canonicalize_terms(&mut arena_unwrapped, &[reflexive]).unwrap();

        let (wrapped, delta) = canonicalize_terms_with_stats(&mut arena, &[reflexive]).unwrap();
        assert_eq!(
            wrapped, direct,
            "the stats wrapper must not change canonicalize_terms's own output"
        );
        // `x = x` canonicalizes to the constant `true`: strictly smaller.
        assert!(wrapped.changed());
        assert!(delta.after.dag_nodes < delta.before.dag_nodes);
        assert!(delta.dag_node_delta() < 0);
    }

    #[test]
    fn eliminate_arrays_with_stats_matches_unwrapped_and_grows_the_dag() {
        let mut arena = TermArena::new();
        let arr = arena.array_var("a", 8, 8).unwrap();
        let i = arena.bv_var("i", 8).unwrap();
        let j = arena.bv_var("j", 8).unwrap();
        // Two selects on the same free array at unrelated indices: no
        // read-over-write applies, so this forces the Ackermann
        // select-consistency path (`idx_i = idx_j => fresh_i = fresh_j`),
        // which strictly grows the DAG with fresh symbols and an implication.
        let select_i = arena.select(arr, i).unwrap();
        let select_j = arena.select(arr, j).unwrap();
        let assertion = arena.eq(select_i, select_j).unwrap();

        let mut arena_unwrapped = arena.clone();
        let direct =
            crate::eliminate_arrays(&mut arena_unwrapped, std::slice::from_ref(&assertion))
                .unwrap();

        let (wrapped, delta) =
            eliminate_arrays_with_stats(&mut arena, std::slice::from_ref(&assertion)).unwrap();
        assert_eq!(
            wrapped.assertions(),
            direct.assertions(),
            "the stats wrapper must not change eliminate_arrays's own output"
        );
        assert!(wrapped.had_arrays());
        assert_eq!(wrapped.selects().len(), 2);
        assert!(
            delta.after.dag_nodes > delta.before.dag_nodes,
            "Ackermann select-consistency constraints must grow the DAG: {delta:?}"
        );
    }

    #[test]
    fn eliminate_int_divmod_with_stats_matches_unwrapped_and_grows_the_dag() {
        let mut arena = TermArena::new();
        let a = arena.int_var("a").unwrap();
        let c = arena.int_const(3);
        let q = arena.int_div(a, c).unwrap();
        let zero = arena.int_const(0);
        let assertion = arena.int_ge(q, zero).unwrap();

        let mut arena_unwrapped = arena.clone();
        let direct = crate::eliminate_int_divmod(&mut arena_unwrapped, &[assertion]).unwrap();

        let (wrapped, delta) = eliminate_int_divmod_with_stats(&mut arena, &[assertion]).unwrap();
        assert_eq!(
            wrapped.assertions(),
            direct.assertions(),
            "the stats wrapper must not change eliminate_int_divmod's own output"
        );
        assert!(wrapped.eliminated_any());
        assert!(
            delta.after.dag_nodes > delta.before.dag_nodes,
            "linearizing div/mod adds fresh symbols and defining constraints"
        );
    }

    #[test]
    fn rule_application_counts_matches_the_report_and_is_deterministically_ordered() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let refl = arena.eq(x, x).unwrap();
        let not_refl = arena.not(refl).unwrap();
        let both = arena.and(refl, not_refl).unwrap();
        let outcome = crate::canonicalize(&mut arena, both).unwrap();

        let counts = rule_application_counts(&outcome.report);
        let total: u64 = counts.iter().map(|(_, n)| *n).sum();
        assert_eq!(
            total,
            outcome.report.applications().len() as u64,
            "per-rule counts must sum to the report's total application count"
        );
        let mut sorted = counts.clone();
        sorted.sort_by(|a, b| a.0.cmp(&b.0));
        assert_eq!(counts, sorted, "counts must already be rule-id-sorted");
    }
}
