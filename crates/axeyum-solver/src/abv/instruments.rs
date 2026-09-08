//! Opt-in, clock-free counters for the `QF_ABV` array routes.
//!
//! # Why this exists
//!
//! `QF_ABV` is dispatched through three routes in sequence
//! (`crate::auto::check_auto`): the online `UFBV` CDCL(T) route
//! (`abv-online-cdclt`), then the lazy read-over-write / extensionality CEGAR
//! (`array-fast-path`), then the eager elimination fallback
//! (`qf-abv-array-decline`). Each is recorded in [`crate::RouteTrace`] **when it
//! returns**, and the route that consumes a lost file's budget is exactly the
//! one that does not return: measured 2026-09-08 on the committed 19-file
//! `QF_ABV` loss list, `bmc-arrays/bubbleSort.smt2` was killed by the watchdog
//! inside `abv-online-cdclt` with three attempts recorded, none of them that
//! route. The trail said `bound_by=fd:parse … 20ms` for a file that spent 25
//! seconds somewhere else.
//!
//! The two questions a route trail structurally cannot answer for this
//! division are therefore:
//!
//! 1. **Which array route was running when the clock ran out** — an entered
//!    route with no return publishes nothing, so its absence from the trail
//!    reads identically to "never tried".
//! 2. **What the route was doing** — the eager Ackermann pairing is quadratic
//!    in the selects on one array, the lazy CEGAR's per-round violation scan is
//!    quadratic in ROW sites, and a wall-clock number cannot distinguish "the
//!    SAT search is hard" from "the refinement loop spent the budget deciding
//!    which lemma to add".
//!
//! Both are counts, so both are answered without a clock. Every field here is a
//! count or a flag; timing stays in [`crate::RouteTrace`], deliberately, so a
//! reader never has two clocks to reconcile — the same convention
//! `crate::UfArithOverboundStats` follows.
//!
//! # A resource refusal that reads as a fragment refusal
//!
//! [`AbvStats::row_site_cap_refusals`] is the counter this module was written
//! for. Hitting `MAX_ROW_SITES` inside the lazy-ROW abstraction returns
//! `Ok(None)`, indistinguishable at the call site from "this array read is a
//! shape we do not model" — and the caller then reports
//! *"lazy-ROW declines: an array read is outside the modelled
//! store/variable/const-array fragment"*. A capacity refusal wearing a
//! capability refusal's message is the exact defect class this repository's
//! measurement rules warn about: the printed reason is not the operative one.
//! A nonzero count here says the message is about a bound, not a fragment.
//!
//! # Cost when off
//!
//! One thread-local `Cell<bool>` read per recording site, and nothing else: no
//! clock read, no allocation, no atomic. Nothing is collected unless a caller
//! constructs an [`AbvStatsGuard`], which `axeyum-bench`'s `smtcomp_cli` does
//! only under `--trace`.

use std::cell::Cell;

std::thread_local! {
    /// Whether array-route counters are being collected on this thread.
    static COLLECT_ABV_STATS: Cell<bool> = const { Cell::new(false) };
    /// The counters accumulated since the active guard was created.
    static ABV_STATS: Cell<AbvStats> = const { Cell::new(AbvStats::ZERO) };
}

/// Clock-free counters for the `QF_ABV` array routes.
///
/// Every field is a count. See the module docs for why there is no duration
/// here and why [`Self::row_site_cap_refusals`] is the field this type exists
/// for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub struct AbvStats {
    /// Entries into the online `UFBV` CDCL(T) route (`abv-online-cdclt`).
    pub online_entered: u32,
    /// Of those, the ones that returned. `online_entered > online_returned`
    /// means the query was inside that route when the reading was taken —
    /// which, under a watchdog kill, is the answer to "where did the budget
    /// go" that the route trail cannot give.
    pub online_returned: u32,
    /// Entries into the lazy ROW/extensionality CEGAR (`array-fast-path`).
    pub lazy_entered: u32,
    /// Of those, the ones that returned.
    pub lazy_returned: u32,
    /// Array-reduction calls that ran to completion —
    /// `axeyum_rewrite::eliminate_arrays` (the eager form, which materialises
    /// the full Ackermann constraint set) and `abstract_arrays` (the same
    /// read-over-write rewrite without the quadratic pairing) together.
    pub array_reduction_calls: u32,
    /// Array-reduction calls that returned an error — in practice
    /// `ArrayElimError::Unsupported`, the admission test that routes a query to
    /// the lazy path. Together with [`Self::array_reduction_calls`] this is
    /// every call made.
    pub array_reduction_refusals: u32,
    /// Eager select-congruence (Ackermann) constraints materialised into the
    /// arena. Quadratic in the selects on one array symbol, so this is the
    /// counter that says whether the eager reduction was affordable on this
    /// query.
    ///
    /// **Nonzero on a query the lazy path decides means work was built and
    /// discarded**: the lazy routes need only the abstraction. That was the
    /// state this counter was added in — measured 2026-09-08 at 1,233,416 pairs
    /// built *twice* on `klee-selected-smt2/cu-large-qids/_lbracket-query-052.smt2`,
    /// once by the admission test and once by the route it admitted to, with
    /// neither copy used.
    pub eager_ackermann_pairs: u64,
    /// `select`/store-resolution sites the lazy-ROW abstraction materialised.
    pub row_sites: u32,
    /// Of those, sites resolving a read through a `store`.
    pub row_store_sites: u32,
    /// Times a site was refused because `MAX_ROW_SITES` was already reached.
    /// **Nonzero means the route's "outside the modelled fragment" message is
    /// about a bound, not a fragment** — see the module docs.
    pub row_site_cap_refusals: u32,
    /// CEGAR refinement rounds entered across the array routes.
    pub cegar_rounds: u32,
    /// Candidate `(site, site)` pairs examined by the per-round violation scan
    /// — quadratic only *within* one index-value bucket, since the scan groups
    /// by the index's value rather than walking every pair. This is what
    /// distinguishes "the scalar search is hard" from "the refinement loop
    /// spent the budget looking for a lemma", and reading it against
    /// [`Self::row_sites`] is what shows the grouping is working: before the
    /// grouping landed, `bmc-arrays/bubbleSort.smt2` scanned 722,240 pairs and
    /// evaluated 1,444,400 indices in six rounds, and was killed by the
    /// watchdog.
    pub congruence_pairs_scanned: u64,
    /// Index-term evaluations the select-congruence violation scan performed:
    /// one per DISTINCT index term on an array carrying at least two of them.
    ///
    /// The pairwise scan this replaced evaluated *two* per candidate pair, and
    /// this counter is how that shows: measured 2026-09-08 at 147,940,030
    /// evaluations for 35 lemmas on
    /// `klee-selected-smt2/cu-no-caches/_csplit-query-000018.smt2`, a file we
    /// lose.
    pub index_evals: u64,
    /// Read-over-write lemmas added on demand.
    pub row_lemmas: u32,
    /// Select-congruence lemmas added on demand.
    pub congruence_lemmas: u32,
    /// Extensionality (diff-skolem) witnesses introduced.
    pub diff_skolems: u32,
}

impl AbvStats {
    /// The all-zero counters, so the thread-local can be a `const` initializer.
    pub(crate) const ZERO: Self = Self {
        online_entered: 0,
        online_returned: 0,
        lazy_entered: 0,
        lazy_returned: 0,
        array_reduction_calls: 0,
        array_reduction_refusals: 0,
        eager_ackermann_pairs: 0,
        row_sites: 0,
        row_store_sites: 0,
        row_site_cap_refusals: 0,
        cegar_rounds: 0,
        congruence_pairs_scanned: 0,
        index_evals: 0,
        row_lemmas: 0,
        congruence_lemmas: 0,
        diff_skolems: 0,
    };

    /// Whether any array route was reached at all on this thread.
    ///
    /// A caller uses this to decide whether printing the line is informative: a
    /// row of zeros on a `QF_BV` file says only "this query has no arrays",
    /// which the absence of the line already says.
    #[must_use]
    pub fn engaged(&self) -> bool {
        self.online_entered > 0 || self.lazy_entered > 0 || self.array_reduction_calls > 0
    }

    /// The route that was still running when this reading was taken, if any.
    ///
    /// `None` when every entered route returned. This is the field a watchdog
    /// kill is read for, and it is derived from the entry/return counters
    /// rather than stored, so it cannot disagree with them.
    #[must_use]
    pub fn in_flight_route(&self) -> Option<&'static str> {
        if self.online_entered > self.online_returned {
            Some("abv-online-cdclt")
        } else if self.lazy_entered > self.lazy_returned {
            Some("array-fast-path")
        } else {
            None
        }
    }

    /// One `;`-prefixed `--trace` line, in the `key=value` shape every other
    /// instrument in this tree prints.
    #[must_use]
    pub fn trace_line(&self) -> String {
        format!(
            "; abv in_flight={} online_entered={} online_returned={} lazy_entered={} \
             lazy_returned={} array_reduction_calls={} array_reduction_refusals={} \
             eager_ackermann_pairs={} row_sites={} row_store_sites={} \
             row_site_cap_refusals={} cegar_rounds={} congruence_pairs_scanned={} \
             index_evals={} row_lemmas={} congruence_lemmas={} diff_skolems={}",
            self.in_flight_route().unwrap_or("none"),
            self.online_entered,
            self.online_returned,
            self.lazy_entered,
            self.lazy_returned,
            self.array_reduction_calls,
            self.array_reduction_refusals,
            self.eager_ackermann_pairs,
            self.row_sites,
            self.row_store_sites,
            self.row_site_cap_refusals,
            self.cegar_rounds,
            self.congruence_pairs_scanned,
            self.index_evals,
            self.row_lemmas,
            self.congruence_lemmas,
            self.diff_skolems,
        )
    }
}

/// Enables array-route counter collection on this thread for the lifetime of
/// the guard, resetting the counters on construction and restoring the previous
/// setting on drop.
///
/// Same opt-in, off-by-default convention as [`crate::BvLayerStatsGuard`] and
/// [`crate::UfArithOverboundStatsGuard`]: with no guard live, every recording
/// site reads one thread-local `Cell<bool>` and returns.
pub struct AbvStatsGuard(bool);

impl AbvStatsGuard {
    /// Enables collection for the lifetime of the returned guard.
    #[must_use]
    pub fn enable() -> Self {
        let previous = COLLECT_ABV_STATS.with(|c| c.replace(true));
        ABV_STATS.with(|c| c.set(AbvStats::ZERO));
        AbvStatsGuard(previous)
    }
}

impl Drop for AbvStatsGuard {
    fn drop(&mut self) {
        COLLECT_ABV_STATS.with(|c| c.set(self.0));
    }
}

/// The counters accumulated on this thread since the active [`AbvStatsGuard`]
/// (or the most recently dropped one) was created.
///
/// All-zero means either "collection was never enabled" or "no array route was
/// reached" — the caller knows which, because it decides whether to construct
/// the guard. [`AbvStats::engaged`] answers the second question for a caller
/// that did.
#[must_use]
pub fn last_abv_stats() -> AbvStats {
    ABV_STATS.with(Cell::get)
}

/// Applies `f` to this thread's counters when collection is enabled; otherwise
/// reads one `Cell<bool>` and returns.
///
/// Every recording site in the array routes goes through here, and each one
/// additionally mirrors the updated snapshot onto the cross-thread board so a
/// watchdog on another thread can read it — see
/// [`crate::live_instruments`]. The mirror is inside this function rather than
/// at the call sites for the reason the counters are: a publish a call site can
/// forget is a publish some call site will forget.
pub(crate) fn note_abv(f: impl FnOnce(&mut AbvStats)) {
    if !COLLECT_ABV_STATS.with(Cell::get) {
        return;
    }
    let updated = ABV_STATS.with(|c| {
        let mut stats = c.get();
        f(&mut stats);
        c.set(stats);
        stats
    });
    // `InFlight` unconditionally: this snapshot is taken between two recording
    // sites of a route that has not returned, so it is a lower bound on every
    // counter by construction. The one reading that is *not* partial — the
    // counters as of a completed `solve` — is read straight from
    // [`last_abv_stats`] on the worker's own thread.
    crate::live_instruments::publish_live(
        crate::live_instruments::instrument::ABV,
        updated,
        crate::live_instruments::Sampled::InFlight,
    );
}

#[cfg(test)]
mod tests {
    use super::{AbvStats, AbvStatsGuard, last_abv_stats, note_abv};

    #[test]
    fn counters_are_off_without_a_guard() {
        // No guard: the recording site must not mutate anything. Run the
        // closure that WOULD count, and require the reader still reads zero.
        note_abv(|s| s.online_entered += 1);
        assert_eq!(last_abv_stats(), AbvStats::ZERO);
    }

    #[test]
    fn guard_collects_and_resets() {
        let guard = AbvStatsGuard::enable();
        note_abv(|s| s.online_entered += 1);
        note_abv(|s| s.eager_ackermann_pairs += 4096);
        let stats = last_abv_stats();
        assert_eq!(stats.online_entered, 1);
        assert_eq!(stats.eager_ackermann_pairs, 4096);
        drop(guard);
        // A fresh guard resets, so one query's counters never leak into the
        // next one's line.
        let _guard = AbvStatsGuard::enable();
        assert_eq!(last_abv_stats(), AbvStats::ZERO);
    }

    #[test]
    fn in_flight_route_is_derived_from_entry_and_return() {
        let mut stats = AbvStats::ZERO;
        assert_eq!(stats.in_flight_route(), None);
        stats.online_entered = 1;
        assert_eq!(stats.in_flight_route(), Some("abv-online-cdclt"));
        stats.online_returned = 1;
        assert_eq!(stats.in_flight_route(), None);
        stats.lazy_entered = 1;
        assert_eq!(stats.in_flight_route(), Some("array-fast-path"));
        stats.lazy_returned = 1;
        assert_eq!(stats.in_flight_route(), None);
    }

    #[test]
    fn engaged_separates_no_arrays_from_no_collection() {
        assert!(!AbvStats::ZERO.engaged());
        let mut stats = AbvStats::ZERO;
        stats.array_reduction_calls = 1;
        assert!(stats.engaged());
    }

    #[test]
    fn trace_line_names_every_field() {
        // A field added without a matching key would silently never be
        // printed. Derive the expectation from the count of `=` separators the
        // formatter emits rather than restating the list.
        let line = AbvStats::ZERO.trace_line();
        assert!(line.starts_with("; abv "), "{line}");
        assert_eq!(
            line.matches('=').count(),
            17,
            "every AbvStats field plus in_flight must appear: {line}"
        );
    }
}
