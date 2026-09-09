//! Opt-in, clock-free warmth counters for the lazy-ROW `QF_ABV` CEGAR loop.
//!
//! # Why this exists
//!
//! The refinement loop in [`crate::abv`] grows one `working` set of scalar
//! assertions and solves it once per round. Whether the scalar engine *reuses*
//! round *n*'s encoding in round *n+1* is invisible from outside: a warm solver
//! that silently rebuilt would return the same verdicts, in roughly the same
//! shape, and only wall-clock — the least trustworthy instrument on a shared
//! box — would differ. So the loop records what it did, and a test asserts on
//! the record.
//!
//! The load-bearing field is **not** [`Self::clause_counts`]. A clause count is
//! monotone whether or not the engine is warm: a *fresh* engine at round *n+1*
//! encodes the whole (larger) working set, so its count is also ≥ round *n*'s.
//! Monotonicity alone therefore cannot fail on a cold rebuild, and a check that
//! cannot fail is worse than none.
//!
//! What does fail is the **encode-exactly-once** invariant
//! ([`RowCegarWarmth::encodes_each_assertion_once`]): across the whole loop the
//! warm engine is handed each working assertion exactly one time, so the total
//! handed over equals the final size of the working set. A rebuild re-hands
//! every earlier assertion and the totals separate immediately. Two further
//! guards are derived rather than stored: [`Self::engine_generations`] counts
//! constructions (one warm engine per query, or the loop is not warm) and
//! [`Self::cold_rounds`] counts rounds that fell back to the one-shot backend.
//!
//! # Cost when off
//!
//! One thread-local `Cell<bool>` read per recording site. Nothing is collected
//! unless a caller constructs a [`RowCegarWarmthGuard`].

use std::cell::{Cell, RefCell};

std::thread_local! {
    /// Whether lazy-ROW warmth counters are being collected on this thread.
    static COLLECT_ROW_WARMTH: Cell<bool> = const { Cell::new(false) };
    /// The record accumulated since the active guard was created.
    static ROW_WARMTH: RefCell<RowCegarWarmth> = const {
        RefCell::new(RowCegarWarmth::ZERO)
    };
}

/// What the lazy-ROW CEGAR loop's scalar engine actually did, per round.
///
/// Every field is a count or a per-round count vector; there is no duration
/// here on purpose (see the module docs).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct RowCegarWarmth {
    /// Warm incremental engines constructed. One per query means the loop held
    /// a single engine across every round; more than one means it restarted.
    pub engine_generations: u32,
    /// Refinement rounds the loop ran.
    pub rounds: u32,
    /// Of those, rounds decided by the one-shot backend rather than the warm
    /// engine (the warm engine refused the shape, or was never installed).
    pub cold_rounds: u32,
    /// Total working-set assertions handed to a warm engine across all rounds.
    pub warm_asserted_terms: u64,
    /// Size of the working set as of the last round the loop ran.
    pub working_terms_final: u64,
    /// Retained CNF clause count after each warm round, in round order.
    pub clause_counts: Vec<u64>,
    /// Retained AIG node count after each warm round, in round order.
    pub aig_node_counts: Vec<u64>,
}

impl RowCegarWarmth {
    /// The empty record, so the thread-local can be a `const` initializer.
    pub(crate) const ZERO: Self = Self {
        engine_generations: 0,
        rounds: 0,
        cold_rounds: 0,
        warm_asserted_terms: 0,
        working_terms_final: 0,
        clause_counts: Vec::new(),
        aig_node_counts: Vec::new(),
    };

    /// Whether the lazy-ROW CEGAR loop ran at all under the active guard.
    #[must_use]
    pub fn engaged(&self) -> bool {
        self.rounds > 0
    }

    /// Whether every round after the first reused the previous round's engine:
    /// one construction, no cold fallbacks, at least one round.
    #[must_use]
    pub fn stayed_warm(&self) -> bool {
        self.engaged() && self.engine_generations == 1 && self.cold_rounds == 0
    }

    /// **The falsifiable warmth invariant.** A warm engine is handed each
    /// working assertion exactly once over the life of the loop, so the running
    /// total equals the final working-set size. A round that rebuilds re-hands
    /// everything asserted before it, and the two numbers separate.
    ///
    /// Meaningless (and therefore `false`) when the loop never ran warm.
    #[must_use]
    pub fn encodes_each_assertion_once(&self) -> bool {
        self.stayed_warm() && self.warm_asserted_terms == self.working_terms_final
    }

    /// Whether the retained clause count never decreased from one warm round to
    /// the next — the roadmap's stated criterion. Necessary, not sufficient:
    /// see the module docs for why this cannot fail on a cold rebuild.
    #[must_use]
    pub fn clauses_monotone(&self) -> bool {
        self.clause_counts.windows(2).all(|w| w[0] <= w[1])
    }

    /// Whether the retained lowering (AIG) node count never decreased — the
    /// "lowering map unchanged" half of the criterion, in the only form a
    /// counter can express it.
    #[must_use]
    pub fn lowering_monotone(&self) -> bool {
        self.aig_node_counts.windows(2).all(|w| w[0] <= w[1])
    }

    /// One `;`-prefixed `--trace` line, in the `key=value` shape every other
    /// instrument in this tree prints.
    #[must_use]
    pub fn trace_line(&self) -> String {
        format!(
            "; row-warmth generations={} rounds={} cold_rounds={} warm_asserted={} \
             working_final={} clauses={:?} aig_nodes={:?}",
            self.engine_generations,
            self.rounds,
            self.cold_rounds,
            self.warm_asserted_terms,
            self.working_terms_final,
            self.clause_counts,
            self.aig_node_counts,
        )
    }
}

/// Enables lazy-ROW warmth collection on this thread for the lifetime of the
/// guard, resetting the record on construction and restoring the previous
/// setting on drop.
///
/// Same opt-in, off-by-default convention as [`crate::AbvStatsGuard`].
pub struct RowCegarWarmthGuard(bool);

impl RowCegarWarmthGuard {
    /// Enables collection for the lifetime of the returned guard.
    #[must_use]
    pub fn enable() -> Self {
        let previous = COLLECT_ROW_WARMTH.with(|c| c.replace(true));
        ROW_WARMTH.with(|c| *c.borrow_mut() = RowCegarWarmth::ZERO);
        RowCegarWarmthGuard(previous)
    }
}

impl Drop for RowCegarWarmthGuard {
    fn drop(&mut self) {
        COLLECT_ROW_WARMTH.with(|c| c.set(self.0));
    }
}

/// The record accumulated on this thread since the active
/// [`RowCegarWarmthGuard`] (or the most recently dropped one) was created.
#[must_use]
pub fn last_row_cegar_warmth() -> RowCegarWarmth {
    ROW_WARMTH.with(|c| c.borrow().clone())
}

/// Applies `f` to this thread's record when collection is enabled; otherwise
/// reads one `Cell<bool>` and returns.
pub(crate) fn note_row_warmth(f: impl FnOnce(&mut RowCegarWarmth)) {
    if !COLLECT_ROW_WARMTH.with(Cell::get) {
        return;
    }
    ROW_WARMTH.with(|c| f(&mut c.borrow_mut()));
}

#[cfg(test)]
mod tests {
    use super::{RowCegarWarmth, RowCegarWarmthGuard, last_row_cegar_warmth, note_row_warmth};

    #[test]
    fn counters_are_off_without_a_guard() {
        note_row_warmth(|w| w.rounds += 1);
        assert_eq!(last_row_cegar_warmth(), RowCegarWarmth::ZERO);
    }

    #[test]
    fn guard_collects_and_resets() {
        let guard = RowCegarWarmthGuard::enable();
        note_row_warmth(|w| {
            w.engine_generations += 1;
            w.rounds += 1;
            w.clause_counts.push(17);
        });
        let record = last_row_cegar_warmth();
        assert_eq!(record.engine_generations, 1);
        assert_eq!(record.clause_counts, vec![17]);
        drop(guard);
        let _guard = RowCegarWarmthGuard::enable();
        assert_eq!(last_row_cegar_warmth(), RowCegarWarmth::ZERO);
    }

    #[test]
    fn encode_once_separates_warm_from_a_rebuild() {
        // Three rounds over a working set that grows 4 -> 6 -> 7.
        // Warm: 4 + 2 + 1 = 7 terms handed over, final size 7.
        let warm = RowCegarWarmth {
            engine_generations: 1,
            rounds: 3,
            cold_rounds: 0,
            warm_asserted_terms: 7,
            working_terms_final: 7,
            clause_counts: vec![10, 14, 16],
            aig_node_counts: vec![20, 26, 29],
        };
        assert!(warm.stayed_warm());
        assert!(warm.encodes_each_assertion_once());
        assert!(warm.clauses_monotone());
        assert!(warm.lowering_monotone());

        // A rebuild at every round re-hands everything: 4 + 6 + 7 = 17.
        // The clause counts are STILL monotone -- that is the whole point of
        // not resting the check on them.
        let rebuilt = RowCegarWarmth {
            engine_generations: 3,
            warm_asserted_terms: 17,
            ..warm.clone()
        };
        assert!(
            rebuilt.clauses_monotone(),
            "monotonicity cannot see a rebuild"
        );
        assert!(!rebuilt.stayed_warm());
        assert!(!rebuilt.encodes_each_assertion_once());

        // Even with the generation counter fooled, the totals still separate.
        let miscounted = RowCegarWarmth {
            engine_generations: 1,
            warm_asserted_terms: 17,
            ..warm.clone()
        };
        assert!(miscounted.stayed_warm());
        assert!(!miscounted.encodes_each_assertion_once());
    }

    #[test]
    fn a_loop_that_never_ran_is_not_warm() {
        assert!(!RowCegarWarmth::ZERO.engaged());
        assert!(!RowCegarWarmth::ZERO.stayed_warm());
        assert!(!RowCegarWarmth::ZERO.encodes_each_assertion_once());
    }
}
