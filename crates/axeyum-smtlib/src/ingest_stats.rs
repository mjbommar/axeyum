//! Opt-in, thread-local SMT-LIB ingest counters: atoms and lists the
//! [`crate::sexpr::read_all`] tokenizer produced, the maximum s-expression
//! nesting depth it saw, and — from the typed parser — the number of
//! top-level forms, assertions, and declared symbols/sorts.
//!
//! This exists to answer the question a prior lane left open
//! (`docs/research/12-performance/bench-primitives-2026-09-07.md`, Finding
//! 2): the in-tree "58 MB takes ~54 s" figure predicts a rate about 30x
//! slower than four committed files (2.7 KB – 10.5 MB) measure, and the file
//! itself is not in the tree to settle which of "the file's *shape* is the
//! cost" / "the figure is stale" / "the 54 s covers more than
//! `parse_script`" is true. These counters let a caller check the **shape**
//! hypothesis directly — an adversarial file with a huge atom/list count or
//! nesting depth relative to its byte size is distinguishable from an
//! ordinary one without needing the original file (see
//! `docs/research/12-performance/foundation-counters-2026-09-07.md`).
//!
//! Same convention as `axeyum_solver::smtlib`'s `FrontDoorStatsGuard` /
//! `cdclt::TheoryLayerStatsGuard` / `layers::BvLayerStatsGuard`: a
//! thread-local `Cell<bool>` flag, a guard that flips it and resets the
//! accumulators for its lifetime, and a free function to read the
//! accumulated snapshot. Counting is opt-in and clock-free: every increment
//! site checks the flag first, so ingest with no guard active is
//! byte-identical to a build with this module deleted (asserted by
//! `tests::counting_does_not_change_parse_output` in `lib.rs`).

use std::cell::Cell;

thread_local! {
    static COLLECTING: Cell<bool> = const { Cell::new(false) };
    static ATOMS: Cell<u64> = const { Cell::new(0) };
    static LISTS: Cell<u64> = const { Cell::new(0) };
    static MAX_DEPTH: Cell<u64> = const { Cell::new(0) };
    static TOP_LEVEL_FORMS: Cell<u64> = const { Cell::new(0) };
    static ASSERTIONS: Cell<u64> = const { Cell::new(0) };
    static SYMBOLS_DECLARED: Cell<u64> = const { Cell::new(0) };
    static SORTS_DECLARED: Cell<u64> = const { Cell::new(0) };
}

/// Whether ingest counting is enabled on this thread. Checked at every
/// increment site in [`crate::sexpr`] and [`crate::parse`] before touching
/// any counter.
pub(crate) fn collecting() -> bool {
    COLLECTING.with(Cell::get)
}

/// Records one atom or list token ([`crate::sexpr::SExpr`]) produced by
/// [`crate::sexpr::read_all`]'s `emit` closure. Self-gated on [`collecting`]
/// so call sites in the tokenizer's hot loop stay one-liners.
pub(crate) fn record_emitted(expr: &crate::sexpr::SExpr) {
    if !collecting() {
        return;
    }
    match expr {
        crate::sexpr::SExpr::Atom(_) => ATOMS.with(|c| c.set(c.get() + 1)),
        crate::sexpr::SExpr::List(_) => LISTS.with(|c| c.set(c.get() + 1)),
    }
}

/// Records the open-paren stack depth just after a `(` was pushed, updating
/// the running maximum. Self-gated on [`collecting`].
pub(crate) fn record_depth(depth: usize) {
    if !collecting() {
        return;
    }
    let depth = depth as u64;
    MAX_DEPTH.with(|c| {
        if depth > c.get() {
            c.set(depth);
        }
    });
}

/// Records the number of top-level s-expressions [`crate::sexpr::read_all`]
/// returned for one script. Self-gated on [`collecting`].
pub(crate) fn record_top_level_forms(n: u64) {
    if !collecting() {
        return;
    }
    TOP_LEVEL_FORMS.with(|c| c.set(c.get() + n));
}

/// Records the number of assertions the typed parser produced for one
/// script, plus the arena's external-symbol and uninterpreted-sort table
/// sizes at the end of that parse. Self-gated on [`collecting`].
pub(crate) fn record_script_totals(assertions: u64, symbols_declared: u64, sorts_declared: u64) {
    if !collecting() {
        return;
    }
    ASSERTIONS.with(|c| c.set(c.get() + assertions));
    SYMBOLS_DECLARED.with(|c| c.set(c.get() + symbols_declared));
    SORTS_DECLARED.with(|c| c.set(c.get() + sorts_declared));
}

/// Enables [`IngestStats`] collection for every [`crate::parse_script`] /
/// [`crate::sexpr::read_all`] call on this thread for the lifetime of the
/// returned guard, restoring the previous setting on drop. Resets every
/// accumulator to zero on `enable()`, so each guard's lifetime reports only
/// what happened while it was live.
pub struct IngestStatsGuard(bool);

impl IngestStatsGuard {
    /// Enables collection for the lifetime of the returned guard.
    #[must_use]
    pub fn enable() -> Self {
        let previous = COLLECTING.with(|c| c.replace(true));
        ATOMS.with(|c| c.set(0));
        LISTS.with(|c| c.set(0));
        MAX_DEPTH.with(|c| c.set(0));
        TOP_LEVEL_FORMS.with(|c| c.set(0));
        ASSERTIONS.with(|c| c.set(0));
        SYMBOLS_DECLARED.with(|c| c.set(0));
        SORTS_DECLARED.with(|c| c.set(0));
        IngestStatsGuard(previous)
    }
}

impl Drop for IngestStatsGuard {
    fn drop(&mut self) {
        COLLECTING.with(|c| c.set(self.0));
    }
}

/// The ingest counters accumulated on this thread since the active
/// [`IngestStatsGuard`] (or the most recently dropped one) was created.
///
/// Reading is independent of whether the guard is still live, mirroring
/// `axeyum_solver::smtlib::last_front_door_stats`. All zero when counting was
/// never enabled on this thread.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct IngestStats {
    /// Atom tokens the tokenizer produced.
    pub atoms: u64,
    /// Lists the tokenizer closed.
    pub lists: u64,
    /// Deepest open-paren nesting the tokenizer saw.
    pub max_sexpr_depth: u64,
    /// Top-level s-expressions (commands) the tokenizer returned.
    pub top_level_forms: u64,
    /// Assertions the typed parser produced.
    pub assertions: u64,
    /// External symbols declared in the arena by the end of the parse.
    pub symbols_declared: u64,
    /// Uninterpreted sorts declared in the arena by the end of the parse.
    pub sorts_declared: u64,
}

/// Reads the [`IngestStats`] accumulated on this thread. See the struct doc
/// for when this is meaningful.
#[must_use]
pub fn last_ingest_stats() -> IngestStats {
    IngestStats {
        atoms: ATOMS.with(Cell::get),
        lists: LISTS.with(Cell::get),
        max_sexpr_depth: MAX_DEPTH.with(Cell::get),
        top_level_forms: TOP_LEVEL_FORMS.with(Cell::get),
        assertions: ASSERTIONS.with(Cell::get),
        symbols_declared: SYMBOLS_DECLARED.with(Cell::get),
        sorts_declared: SORTS_DECLARED.with(Cell::get),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A script with an uninterpreted sort, an array, and bit-vectors, so
    /// `parse_script` exercises every arena table this module counts.
    const SAMPLE: &str = "\
        (declare-sort U 0) \
        (declare-const u U) \
        (declare-const x (_ BitVec 8)) \
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8))) \
        (assert (= x #x2a)) \
        (assert (= (select a x) x)) \
        (assert (= u u)) \
        (check-sat)";

    /// Enabling [`IngestStatsGuard`] over a script that uses several arena
    /// tables must report nonzero atoms, lists, nesting depth, top-level
    /// forms, assertions, and a declared symbol/sort table.
    #[test]
    fn enabling_ingest_stats_counts_real_parse_work() {
        let _guard = IngestStatsGuard::enable();
        let script = crate::parse_script(SAMPLE).expect("SAMPLE parses");
        let stats = last_ingest_stats();
        assert!(stats.atoms > 0, "{stats:?}");
        assert!(stats.lists > 0, "{stats:?}");
        assert!(stats.max_sexpr_depth >= 2, "{stats:?}");
        assert!(stats.top_level_forms >= 7, "{stats:?}");
        assert_eq!(stats.assertions, script.assertions.len() as u64);
        assert!(stats.symbols_declared > 0, "{stats:?}");
        assert!(stats.sorts_declared > 0, "{stats:?}");
    }

    /// Parsing on a thread with no active [`IngestStatsGuard`] must not move
    /// any counter. Establishes a known zero baseline first (via a
    /// throwaway guard) so this does not depend on whether `cargo test`
    /// reused this OS thread for an earlier, counting-enabled test.
    #[test]
    fn counting_off_leaves_ingest_stats_untouched_by_parsing() {
        {
            let _reset = IngestStatsGuard::enable();
        }
        assert!(
            !collecting(),
            "the guard must restore the prior (off) state"
        );
        let before = last_ingest_stats();
        let _ = crate::parse_script(SAMPLE).expect("SAMPLE parses");
        let after = last_ingest_stats();
        assert_eq!(
            before, after,
            "parse_script with no active guard must not touch any ingest counter"
        );
    }

    /// The non-negotiable from the counters brief: enabling collection must
    /// not change what `parse_script` returns. Compares both the flat
    /// assertion count and the exported text, since [`crate::Script`] itself
    /// has no `PartialEq`.
    #[test]
    fn counting_does_not_change_parse_output() {
        let counted = {
            let _guard = IngestStatsGuard::enable();
            crate::parse_script(SAMPLE).expect("SAMPLE parses")
        };
        let uncounted = crate::parse_script(SAMPLE).expect("SAMPLE parses");

        assert_eq!(counted.assertions.len(), uncounted.assertions.len());
        assert_eq!(counted.check_sats, uncounted.check_sats);
        assert_eq!(counted.logic, uncounted.logic);
        let counted_text = crate::write_script(&counted.arena, &counted.assertions);
        let uncounted_text = crate::write_script(&uncounted.arena, &uncounted.assertions);
        assert_eq!(
            counted_text, uncounted_text,
            "enabling IngestStatsGuard must not change parse_script's output"
        );
    }
}
