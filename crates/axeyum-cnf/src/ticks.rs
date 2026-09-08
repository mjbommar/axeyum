//! The deterministic tick: a cache-aware proxy for search work.
//!
//! A budget needs a unit. Conflicts are too coarse (a conflict on a 10-clause
//! formula and one on a 10-million-clause formula are not the same amount of
//! work), propagations ignore where the memory traffic actually goes, and wall
//! time is not reproducible. The unit both reference solvers converged on is a
//! **tick**: one expected cache line touched during propagation
//! (`kissat/src/utilities.h:19-34`, `cadical/src/internal.hpp:739-742`).
//!
//! Two properties make it the right unit, and this module preserves both:
//!
//! * **It tracks the thing that dominates runtime.** A sequential scan of a
//!   contiguous watch list is cheap per element, so it is amortised over a
//!   cache line; every *pointer chase somewhere else in memory* — the clause
//!   arena, another watch list, the per-conflict mark array — costs a full
//!   tick each.
//! * **It is machine-independent.** The cache line is a *compile-time
//!   assumption*, never a query of the host. Nothing here reads a clock, an
//!   allocator address, or the CPU's real geometry, so a fixed formula and
//!   fixed options produce a fixed tick count on any machine — which is exactly
//!   the property a `deadline: Option<Instant>` cannot give.
//!
//! # This model is derived, and adds nothing to the hot path
//!
//! Kissat charges ticks inline in its propagator. We do not need to: we already
//! count the raw quantities ([`SearchCounters`], gated behind the same opt-in
//! `count_search` flag), and a tick count is an exact arithmetic function of
//! them. **So the tick model costs zero instructions in `propagate`** — it is
//! evaluated once at a round boundary, out of the hot loop entirely.
//!
//! Where the derivation approximates, it does so in one identified place. Kissat
//! charges `1 + ceil(n/W)` on *entering* a watch list of `n` entries; we know
//! how many watch entries were examined in total ([`SearchCounters::watch_visits`])
//! and how many lists were entered (one per literal dequeued from the
//! propagation trail, i.e. [`SearchCounters::decisions`] +
//! [`SearchCounters::propagations`]), so we charge the base term per list and
//! amortise the whole scan over cache lines once. The difference between
//! `sum(ceil(n_i/W))` and `ceil(sum(n_i)/W)` is at most one tick per list, and
//! the per-list base term is already the leading component — so the two agree
//! to within a factor the assumed line size itself does not justify resolving.
//! The list count is also a slight over-estimate: a `propagate` that returns on
//! a conflict leaves trail entries unvisited. Both are properties of a *cost
//! model*, not defects: the 128-byte line is itself an assumption, and what a
//! budget needs is a deterministic quantity that rises with real work.
//!
//! # Where this model differs from Kissat's, deliberately
//!
//! [`crate::ticks::TickModel::DEFAULT`] charges one term Kissat has no counterpart for: the
//! per-conflict mark array `analyze` allocates and zeroes, which is
//! `conflicts x variables` bytes and is *the* cost in this core that scales
//! with the formula rather than with the conflict. Leaving a known
//! formula-scaled cost out of a cost model makes the model wrong about exactly
//! the instances where budgeting matters most. [`crate::ticks::TickModel::PROPAGATION_ONLY`]
//! omits it, for when the point is to compare our tick counts against a
//! reference solver's rather than to budget our own work.
//!
//! # Feeding a budget
//!
//! This module deliberately returns a plain `u64` and does not depend on
//! `axeyum-ir`: `axeyum-cnf`'s library dependency graph is one crate wide and
//! keeping it that way is worth more than a convenience constructor. A caller
//! that holds the budget primitive wraps the total itself —
//! `WorkMeter::at(counters.ticks())` for a fresh meter, or
//! `meter.advance_to(counters.ticks())` for one that mirrors a running search.

use crate::proof_sat::{SearchCounters, WATCH_BYTES};

/// The assumed cache line, in bytes.
///
/// A **compile-time constant, not a measurement of the host** — that is what
/// makes the tick count portable. Both reference solvers assume 128 bytes,
/// which is 2x a typical x86 line; the doubling is deliberate slack, and the
/// exact value matters far less than that every machine uses the same one.
pub const ASSUMED_CACHE_LINE_BYTES: u64 = 128;

/// Watch entries that fit one assumed cache line.
///
/// Derived from **our** `Watch` (a tagged clause reference plus a blocking
/// literal), not copied from Kissat's number: their watch is a 4-byte tagged
/// word, so they amortise over 32 and we over 8. `proof_sat.rs` carries a
/// compile-time assertion that `Watch` really is `WATCH_BYTES` wide, so growing
/// the watch breaks the build rather than silently re-denominating every budget
/// calibrated in ticks.
///
/// The 2026-09 binary-watch change (Kissat's `watch.h:18-42`) deliberately
/// packed its tag into bit 0 of the clause reference rather than adding a
/// field, precisely so this constant did **not** move: it removes clause
/// dereferences (the `clause_deref` term measures fewer events) without
/// changing what a tick is denominated in. Kissat's other saving — a *binary*
/// watch being half the width of a long one, so binary-heavy lists scan denser
/// — is not available under a fixed-stride watch array and is not claimed
/// here.
pub const WATCHES_PER_CACHE_LINE: u64 = ASSUMED_CACHE_LINE_BYTES / WATCH_BYTES as u64;

/// The charging rules that turn [`SearchCounters`] into ticks.
///
/// Every field is a whole-number weight, so a tick count is exact integer
/// arithmetic with no rounding rule to differ between hosts. The weights are
/// public and nameable so a measurement can say which model produced a number
/// — a tick is only comparable to another tick charged the same way.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TickModel {
    /// Charged once per watch list entered: the pointer chase to the list
    /// header, before any of its entries are read.
    pub watch_list_entry: u64,
    /// Watch entries amortised into one tick — the sequential-scan term.
    /// Must not be zero.
    pub watches_per_cache_line: u64,
    /// Charged per watch whose clause had to be dereferenced: a chase into the
    /// clause arena. The blocking literal is what avoids this, so the
    /// difference from `watch_visits` is what the blocker optimisation saves.
    pub clause_deref: u64,
    /// Charged per watch moved to a different literal's list: a push into
    /// another allocation.
    pub watch_relocation: u64,
    /// Charged per antecedent clause walked by `analyze`.
    pub reason_walk: u64,
    /// Bytes of `analyze`'s per-conflict mark array amortised into one tick.
    /// `0` disables the term entirely — see the module docs for why the default
    /// keeps it.
    pub analyze_mark_bytes_per_line: u64,
}

impl TickModel {
    /// The shipping model: propagation traffic plus `analyze`'s per-conflict
    /// mark array, which is this core's one formula-scaled per-conflict cost.
    pub const DEFAULT: Self = Self {
        watch_list_entry: 1,
        watches_per_cache_line: WATCHES_PER_CACHE_LINE,
        clause_deref: 1,
        watch_relocation: 1,
        reason_walk: 1,
        analyze_mark_bytes_per_line: ASSUMED_CACHE_LINE_BYTES,
    };

    /// The Kissat-shaped subset: propagation and conflict-analysis traffic
    /// only, with no term for the mark array. Use this when the number is going
    /// to be compared against a reference solver's `ticks` statistic; use
    /// [`TickModel::DEFAULT`] when it is going to be used as a budget.
    pub const PROPAGATION_ONLY: Self = Self {
        analyze_mark_bytes_per_line: 0,
        ..Self::DEFAULT
    };

    /// The tick total these counters represent under this model.
    ///
    /// Saturating throughout: an absurd counter degrades to "budget exhausted",
    /// never to a wrapped small number that would look like a fresh budget.
    #[must_use]
    pub fn ticks(&self, counters: &SearchCounters) -> u64 {
        self.breakdown(counters).total()
    }

    /// The tick total, itemised. This is the instrumentation half: a single
    /// number cannot say whether a formula is expensive because of watch-list
    /// length, blocker misses, long reason chains, or the per-conflict memset,
    /// and those have different fixes.
    #[must_use]
    pub fn breakdown(&self, counters: &SearchCounters) -> TickBreakdown {
        // One list is entered per literal dequeued from the propagation trail:
        // every decision and every propagated literal. (Assumptions and
        // root-level units are not counted by `SearchCounters` and so are not
        // charged; a `propagate` cut short by a conflict makes this a slight
        // over-estimate. See the module docs.)
        let lists_entered = counters.decisions.saturating_add(counters.propagations);
        let per_line = self.watches_per_cache_line.max(1);
        TickBreakdown {
            watch_lists: lists_entered.saturating_mul(self.watch_list_entry),
            watch_scan: counters.watch_visits.div_ceil(per_line),
            clause_derefs: counters.clause_visits.saturating_mul(self.clause_deref),
            watch_relocations: counters
                .watch_relocations
                .saturating_mul(self.watch_relocation),
            reason_walks: counters.resolutions.saturating_mul(self.reason_walk),
            analyze_marks: if self.analyze_mark_bytes_per_line == 0 {
                0
            } else {
                counters
                    .analyze_mark_bytes
                    .div_ceil(self.analyze_mark_bytes_per_line)
            },
        }
    }
}

impl Default for TickModel {
    fn default() -> Self {
        Self::DEFAULT
    }
}

/// A tick total, itemised by charging rule. Integer counts only; no clock, so
/// reading it cannot perturb what it measures.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct TickBreakdown {
    /// The per-watch-list base charge.
    pub watch_lists: u64,
    /// The amortised sequential scan of those lists.
    pub watch_scan: u64,
    /// Chases into the clause arena.
    pub clause_derefs: u64,
    /// Watches pushed onto a different literal's list.
    pub watch_relocations: u64,
    /// Antecedent clauses walked by `analyze`.
    pub reason_walks: u64,
    /// `analyze`'s per-conflict mark array, in cache lines.
    pub analyze_marks: u64,
}

impl TickBreakdown {
    /// The sum of every term.
    #[must_use]
    pub fn total(&self) -> u64 {
        self.watch_lists
            .saturating_add(self.watch_scan)
            .saturating_add(self.clause_derefs)
            .saturating_add(self.watch_relocations)
            .saturating_add(self.reason_walks)
            .saturating_add(self.analyze_marks)
    }

    /// The terms, named, in a fixed order — for a report that must not depend
    /// on hash-map iteration order.
    #[must_use]
    pub fn terms(&self) -> [(&'static str, u64); 6] {
        [
            ("watch_lists", self.watch_lists),
            ("watch_scan", self.watch_scan),
            ("clause_derefs", self.clause_derefs),
            ("watch_relocations", self.watch_relocations),
            ("reason_walks", self.reason_walks),
            ("analyze_marks", self.analyze_marks),
        ]
    }
}

impl SearchCounters {
    /// This search's work in ticks, under [`TickModel::DEFAULT`].
    ///
    /// This is the numeraire: the deterministic quantity every inprocessing
    /// budget is denominated as a fraction of. Zero when counting was not
    /// enabled, which is correct — an uncounted search has no measured work to
    /// hand out slices of, and a policy's `min_reference` floor is what covers
    /// that case.
    #[must_use]
    pub fn ticks(&self) -> u64 {
        TickModel::DEFAULT.ticks(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn counters() -> SearchCounters {
        SearchCounters {
            conflicts: 100,
            decisions: 400,
            propagations: 1_600,
            restarts: 3,
            reductions: 1,
            watch_visits: 32_000,
            clause_visits: 4_000,
            watch_relocations: 800,
            resolutions: 900,
            analyze_mark_bytes: 100 * 256,
            redundancy_steps: 50,
            // The clause-database policy landed 21 further counters. This
            // fixture names only the terms the tick model reads, so a new
            // counter cannot break it -- but note the tradeoff: an exhaustive
            // initializer would have FORCED a decision about each new field
            // here. That is the right default for a struct whose fields are
            // load-bearing; it is the wrong one for a test fixture that
            // deliberately exercises a subset.
            ..Default::default()
        }
    }

    #[test]
    fn the_cache_line_constant_comes_from_our_watch_not_kissats() {
        // Our watch is a tagged clause reference plus a blocking literal.
        // Kissat amortises over 32 because theirs is a 4-byte tagged word;
        // copying their number would misprice every scan by 4x. The binary tag
        // rides in bit 0 of the reference, so adding it left this at 16 — the
        // assertion is what makes that a build failure rather than a silent
        // re-denomination of every budget in the tree.
        assert_eq!(WATCH_BYTES, 16);
        assert_eq!(WATCHES_PER_CACHE_LINE, 8);
    }

    #[test]
    fn a_tick_total_is_the_sum_of_named_terms_computed_by_hand() {
        let c = counters();
        let b = TickModel::DEFAULT.breakdown(&c);
        assert_eq!(b.watch_lists, 2_000); // 400 decisions + 1600 propagations
        assert_eq!(b.watch_scan, 4_000); // 32_000 / 8
        assert_eq!(b.clause_derefs, 4_000);
        assert_eq!(b.watch_relocations, 800);
        assert_eq!(b.reason_walks, 900);
        assert_eq!(b.analyze_marks, 200); // 25_600 bytes / 128
        assert_eq!(b.total(), 11_900);
        assert_eq!(TickModel::DEFAULT.ticks(&c), 11_900);
        assert_eq!(c.ticks(), 11_900);
        assert_eq!(b.terms().iter().map(|(_, v)| v).sum::<u64>(), b.total());
    }

    #[test]
    fn the_propagation_only_model_drops_exactly_the_mark_array_term() {
        let c = counters();
        let full = TickModel::DEFAULT.breakdown(&c);
        let kissat_shaped = TickModel::PROPAGATION_ONLY.breakdown(&c);
        assert_eq!(kissat_shaped.analyze_marks, 0);
        assert_eq!(
            kissat_shaped.total() + full.analyze_marks,
            full.total(),
            "the two models must differ in exactly one term"
        );
        // ...and they really do produce different numbers, so a test comparing
        // tick counts is not comparing two names for the same value.
        assert_ne!(kissat_shaped.total(), full.total());
    }

    #[test]
    fn every_weight_moves_the_total_so_none_of_them_is_dead() {
        let c = counters();
        let base = TickModel::DEFAULT.ticks(&c);
        for (name, model) in [
            (
                "watch_list_entry",
                TickModel {
                    watch_list_entry: 2,
                    ..TickModel::DEFAULT
                },
            ),
            (
                "watches_per_cache_line",
                TickModel {
                    watches_per_cache_line: 4,
                    ..TickModel::DEFAULT
                },
            ),
            (
                "clause_deref",
                TickModel {
                    clause_deref: 2,
                    ..TickModel::DEFAULT
                },
            ),
            (
                "watch_relocation",
                TickModel {
                    watch_relocation: 2,
                    ..TickModel::DEFAULT
                },
            ),
            (
                "reason_walk",
                TickModel {
                    reason_walk: 2,
                    ..TickModel::DEFAULT
                },
            ),
            (
                "analyze_mark_bytes_per_line",
                TickModel {
                    analyze_mark_bytes_per_line: 64,
                    ..TickModel::DEFAULT
                },
            ),
        ] {
            assert_ne!(
                model.ticks(&c),
                base,
                "weight `{name}` does not affect the tick total: it is dead \
                 configuration, and the model is not what it claims"
            );
        }
    }

    #[test]
    fn uncounted_counters_yield_zero_ticks() {
        assert_eq!(SearchCounters::default().ticks(), 0);
    }

    #[test]
    fn a_zero_cache_line_divisor_cannot_divide_by_zero() {
        let model = TickModel {
            watches_per_cache_line: 0,
            ..TickModel::DEFAULT
        };
        // Degrades to one tick per watch entry rather than panicking.
        assert_eq!(model.breakdown(&counters()).watch_scan, 32_000);
    }

    #[test]
    fn tick_charging_saturates_rather_than_wrapping() {
        let c = SearchCounters {
            propagations: u64::MAX,
            decisions: u64::MAX,
            watch_visits: u64::MAX,
            ..SearchCounters::default()
        };
        assert_eq!(TickModel::DEFAULT.ticks(&c), u64::MAX);
    }
}
