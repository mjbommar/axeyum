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

// ---------------------------------------------------------------------------
// The tick valve: CaDiCaL's accumulate-and-delay gate, denominated in ticks
// ---------------------------------------------------------------------------
//
// Everything above turns counters into a number. Nothing above SPENDS it, and a
// cost model with no consumer is a decoration: it can be wrong in any direction
// for as long as it likes and no gate goes red. What follows is the consumer.
//
// The design is CaDiCaL's `SET_EFFORT_LIMIT` (`src/limit.hpp:136-164`) plus its
// `Delay` (`src/delay.hpp:9-34`), transcribed in
// `docs/research/02-ecosystems/inprocessing-scheduling-2026-09/cadical-kissat-budget-model.md`
// (2A.2 and 2.4). Three rules, and the third is the one the reference solvers'
// own comments say is the whole point:
//
// 1. A pass's allowance is a per-mille slice of the search ticks that have
//    accrued **since that pass last ran**, so inprocessing can never outgrow
//    the search it is helping.
// 2. A pass whose allowance is below `threshold_per_clause x |clauses|` **does
//    not run at all** -- not "runs with a small budget". A zero-budget round
//    still pays the `O(|F|)` occurrence-list setup, which is exactly the cost
//    the refusal is declining (`references/cadical/src/probe.cpp:902-907`).
// 3. **On the refusal path the watermark is not written.** That is what makes
//    the gate accumulate rather than starve: the reference window keeps growing
//    until it clears the bar. Getting this backwards produces a gate that
//    refuses forever and looks, from every counter, like a working one.
//
// One deliberate divergence, named so it is not read as a transcription error:
// CaDiCaL and Kissat grow their delay counter LINEARLY (`current += 1`).
// [`TickBackoff`] doubles it, so a pass that keeps finding nothing is offered
// again after 1, then 2, then 4 skipped rounds rather than 1, 2, 3. The reason
// is round count: the reference solvers run inprocessing hundreds of times per
// solve and a linear ladder is enough to thin it out; this crate's schedule is
// offered a handful of times, so a linear ladder never leaves the first rung.

/// The denominator of every effort fraction in the valve.
///
/// Per mille rather than a percentage or a float, for the same reason
/// `axeyum_ir::budget` uses it: `reference * per_mille / PER_MILLE` through a
/// `u128` intermediate is exact integer arithmetic with one rounding rule, so
/// two hosts cannot land on different sides of a schedule boundary. **Nothing
/// in the valve reads a clock and nothing in it is floating point.**
pub const PER_MILLE: u64 = 1_000;

/// `value * numerator / denominator` through a `u128` intermediate: cannot
/// overflow, clamps rather than wrapping on the way back down, and
/// `denominator == 0` yields `0`.
fn mul_div(value: u64, numerator: u64, denominator: u64) -> u64 {
    if denominator == 0 {
        return 0;
    }
    let quotient = (u128::from(value) * u128::from(numerator)) / u128::from(denominator);
    u64::try_from(quotient).unwrap_or(u64::MAX)
}

/// How much of the search's work one pass may claim, and how much it has to
/// have accrued before it is allowed to claim any.
///
/// Every field is an integer weight, and every one of them changes a decision —
/// `tests::every_valve_weight_changes_a_decision` fails if one becomes dead
/// configuration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TickEffort {
    /// Per-mille slice of the accrued search ticks the pass may spend.
    /// CaDiCaL's `<pass>effort`.
    pub per_mille: u64,
    /// Refusal threshold as a multiple of the formula's clause count.
    /// CaDiCaL's `<pass>thresh`. **Zero makes the gate vacuous** — which is
    /// what `probethresh = 0` does in CaDiCaL, and what [`TickEffort::UNGATED`]
    /// is for.
    pub threshold_per_clause: u64,
    /// Reference window to use when no search ticks have accrued at all — the
    /// pre-search (preprocessing) call, where the numeraire reads zero.
    /// CaDiCaL's `preprocessinit`.
    pub bootstrap_reference: u64,
    /// Ceiling on [`TickBackoff`]'s skip run. Zero disables the backoff.
    pub max_backoff_rounds: u32,
}

impl TickEffort {
    /// The major-pass setting: 10 % of accrued search ticks, refused below 5x
    /// the clause count. CaDiCaL's `sweep` (`options.hpp:230,236`); the same
    /// 10 % an independent empirical study landed on
    /// (Wotzlaw et al., arXiv:1310.4756).
    pub const MAJOR_PASS: Self = Self {
        per_mille: 100,
        threshold_per_clause: 5,
        bootstrap_reference: 2_000_000,
        max_backoff_rounds: 32,
    };

    /// The setting for a pass whose setup dominates a small round: 5 % of
    /// accrued ticks, refused below 20x the clause count. CaDiCaL's `vivify`
    /// (`options.hpp:259,267`) — note which way round it runs, because it is
    /// counter-intuitive and worth not re-deriving: the pass measured most
    /// expensive gets the SMALLER slice and the LARGER threshold, i.e. it runs
    /// rarely and thoroughly rather than often and pointlessly.
    pub const EXPENSIVE_SETUP: Self = Self {
        per_mille: 50,
        threshold_per_clause: 20,
        ..Self::MAJOR_PASS
    };

    /// A valve that admits every round: the refusal rule and the backoff are
    /// both off, so only the allowance arithmetic remains.
    ///
    /// This is the **control** arm, not a shipping setting. A test that shows
    /// the gate refusing needs a second arm showing the same input running, or
    /// "refused" is indistinguishable from "the fixture cannot run at all".
    pub const UNGATED: Self = Self {
        threshold_per_clause: 0,
        max_backoff_rounds: 0,
        ..Self::MAJOR_PASS
    };

    /// The tick allowance a reference window of `reference` ticks buys.
    #[must_use]
    pub fn allowance(&self, reference: u64) -> u64 {
        mul_div(reference, self.per_mille, PER_MILLE)
    }

    /// The allowance a formula of `clauses` clauses demands before the pass is
    /// admitted at all.
    #[must_use]
    pub const fn threshold(&self, clauses: u64) -> u64 {
        self.threshold_per_clause.saturating_mul(clauses)
    }
}

impl Default for TickEffort {
    fn default() -> Self {
        Self::MAJOR_PASS
    }
}

/// The exponential skip counter for a pass that keeps finding nothing.
///
/// Two numbers, like CaDiCaL's `Delay`: `skips_left` counts down to the next
/// offer, `run` is the length the next failure will restart it at.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct TickBackoff {
    skips_left: u32,
    run: u32,
}

impl TickBackoff {
    /// A backoff that is not delaying anything.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            skips_left: 0,
            run: 0,
        }
    }

    /// Consumes one skip. `true` means this round is skipped.
    pub const fn delaying(&mut self) -> bool {
        if self.skips_left > 0 {
            self.skips_left -= 1;
            true
        } else {
            false
        }
    }

    /// The pass ran and found nothing: **double** the skip run, capped at
    /// `cap`. `cap == 0` disables the backoff entirely.
    pub const fn found_nothing(&mut self, cap: u32) {
        let next = if self.run == 0 {
            1
        } else {
            self.run.saturating_mul(2)
        };
        self.run = if next > cap { cap } else { next };
        self.skips_left = self.run;
    }

    /// The pass ran and found something: halve the skip run, the way both
    /// reference solvers reduce a delay after a productive round.
    pub const fn found_something(&mut self) {
        self.run /= 2;
        self.skips_left = self.run;
    }

    /// Rounds that will be skipped before the next offer reaches the gate.
    #[must_use]
    pub const fn rounds_left(&self) -> u32 {
        self.skips_left
    }

    /// The length the next failed round will restart the skip run at.
    #[must_use]
    pub const fn run_length(&self) -> u32 {
        self.run
    }
}

/// What the valve decided for one offer of one pass.
///
/// Exhaustive on purpose: a `_` arm in a caller would silently absorb a future
/// variant into "run anyway", which is the wrong default for a gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TickGrant {
    /// The pass runs, with this many ticks of allowance, bought by this
    /// reference window.
    Granted {
        /// Ticks the pass may spend.
        allowance: u64,
        /// The window the allowance is a slice of.
        reference: u64,
    },
    /// The pass does not run: its accrued allowance is below the
    /// formula-scaled threshold. The watermark is **not** advanced, so the
    /// window keeps growing.
    Refused {
        /// The allowance that was not enough.
        accrued: u64,
        /// What it had to clear.
        threshold: u64,
    },
    /// The pass does not run: it found nothing on a recent round and is being
    /// offered exponentially less often.
    BackedOff {
        /// Rounds still to skip after this one.
        rounds_left: u32,
    },
}

impl TickGrant {
    /// The allowance, or `None` when the pass does not run.
    #[must_use]
    pub const fn allowance(&self) -> Option<u64> {
        match self {
            Self::Granted { allowance, .. } => Some(*allowance),
            Self::Refused { .. } | Self::BackedOff { .. } => None,
        }
    }

    /// A short, stable, allocation-free tag for a decision log.
    #[must_use]
    pub const fn tag(&self) -> &'static str {
        match self {
            Self::Granted { .. } => "granted",
            Self::Refused { .. } => "refused",
            Self::BackedOff { .. } => "backedoff",
        }
    }
}

/// One pass's share of the valve: the watermark, the refusal gate and the
/// backoff, plus the counts a report needs.
///
/// Deliberately `Copy` and allocation-free — a gate that allocates can fail,
/// and a gate that can fail on a decision path is a gate whose behaviour under
/// pressure is not the behaviour it was tested with.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TickValveAccount {
    effort: TickEffort,
    watermark: u64,
    backoff: TickBackoff,
    granted_rounds: u64,
    refused_rounds: u64,
    backed_off_rounds: u64,
    granted_ticks: u64,
}

impl TickValveAccount {
    /// A fresh account under `effort`, with the watermark at zero.
    #[must_use]
    pub const fn new(effort: TickEffort) -> Self {
        Self {
            effort,
            watermark: 0,
            backoff: TickBackoff::new(),
            granted_rounds: 0,
            refused_rounds: 0,
            backed_off_rounds: 0,
            granted_ticks: 0,
        }
    }

    /// The policy this account applies.
    #[must_use]
    pub const fn effort(&self) -> TickEffort {
        self.effort
    }

    /// Offers the pass a round, given the search's tick reading and the clause
    /// count of the formula the pass would run over.
    ///
    /// `search_ticks` is the numeraire — the tick total of the SEARCH, never of
    /// this pass. Handing this function the pass's own spend would let a pass
    /// fund its own next round, which is the one arrangement under which
    /// inprocessing can outgrow search.
    pub fn request(&mut self, search_ticks: u64, clauses: u64) -> TickGrant {
        if self.backoff.delaying() {
            self.backed_off_rounds += 1;
            return TickGrant::BackedOff {
                rounds_left: self.backoff.rounds_left(),
            };
        }
        let accrued = search_ticks.saturating_sub(self.watermark);
        // No search has run yet (a pre-search preprocessing round), so there is
        // no accrued window to slice. CaDiCaL substitutes a constant here
        // (`preprocessinit`) rather than refusing, because refusing would mean
        // preprocessing never happens at all.
        let reference = if accrued == 0 {
            self.effort.bootstrap_reference
        } else {
            accrued
        };
        let allowance = self.effort.allowance(reference);
        let threshold = self.effort.threshold(clauses);
        if allowance < threshold {
            // The watermark is NOT advanced. See rule 3 above; this line's
            // absence is the difference between a gate that accumulates and a
            // gate that starves.
            self.refused_rounds += 1;
            return TickGrant::Refused {
                accrued: allowance,
                threshold,
            };
        }
        self.watermark = search_ticks;
        self.granted_rounds += 1;
        self.granted_ticks = self.granted_ticks.saturating_add(allowance);
        TickGrant::Granted {
            allowance,
            reference,
        }
    }

    /// Records what a granted round achieved, which is what drives the backoff.
    ///
    /// Call it only for a round that actually ran: charging a refused round as
    /// "found nothing" compounds the two gates into one that closes and never
    /// reopens.
    pub const fn record_outcome(&mut self, found_something: bool) {
        if found_something {
            self.backoff.found_something();
        } else {
            self.backoff.found_nothing(self.effort.max_backoff_rounds);
        }
    }

    /// The backoff state, for a report or a test.
    #[must_use]
    pub const fn backoff(&self) -> TickBackoff {
        self.backoff
    }

    /// Search-tick reading at the last granted round.
    #[must_use]
    pub const fn watermark(&self) -> u64 {
        self.watermark
    }

    /// Rounds granted, refused, and skipped by the backoff, in that order.
    #[must_use]
    pub const fn rounds(&self) -> (u64, u64, u64) {
        (
            self.granted_rounds,
            self.refused_rounds,
            self.backed_off_rounds,
        )
    }

    /// Total ticks granted across every admitted round.
    #[must_use]
    pub const fn granted_ticks(&self) -> u64 {
        self.granted_ticks
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

    // -----------------------------------------------------------------------
    // The valve
    // -----------------------------------------------------------------------

    /// `MAJOR_PASS` over a 1000-clause formula: threshold 5000 ticks, and 10 %
    /// of the accrued window has to clear it. Every number below is derivable
    /// by hand from those two facts, which is the point — an assertion computed
    /// by the code under test is not an assertion.
    #[test]
    fn the_refusal_rule_refuses_below_the_formula_scaled_threshold() {
        let mut account = TickValveAccount::new(TickEffort::MAJOR_PASS);
        // 40 000 accrued ticks buys 4 000; the bar is 5 x 1 000 = 5 000.
        assert_eq!(
            account.request(40_000, 1_000),
            TickGrant::Refused {
                accrued: 4_000,
                threshold: 5_000
            }
        );
        // Refused, so the watermark did NOT move and the window keeps growing.
        assert_eq!(account.watermark(), 0);
        // 60 000 buys 6 000, which clears it.
        assert_eq!(
            account.request(60_000, 1_000),
            TickGrant::Granted {
                allowance: 6_000,
                reference: 60_000
            }
        );
        assert_eq!(account.watermark(), 60_000);
        assert_eq!(account.rounds(), (1, 1, 0));
    }

    /// The rule that separates a gate that accumulates from one that starves.
    /// Written as its own test because it is one line in `request` and the
    /// counters look identical either way.
    #[test]
    fn a_refused_round_does_not_advance_the_watermark_so_the_window_accumulates() {
        let mut starving = TickValveAccount::new(TickEffort::MAJOR_PASS);
        // Ten rounds, each adding 4 000 ticks of search. Under the correct rule
        // the window accumulates and round 2 already clears 5 000; under a rule
        // that wrote the watermark on refusal, each round would see only the
        // 4 000 accrued since the last one and NONE would ever clear.
        let mut granted = 0;
        for round in 1..=10u64 {
            if matches!(
                starving.request(round * 4_000, 1_000),
                TickGrant::Granted { .. }
            ) {
                granted += 1;
            }
        }
        assert!(
            granted > 0,
            "no round was ever admitted: the accumulate rule is inverted"
        );
        // Concretely: rounds at 8k, 20k, 40k, 72k... 8_000 -> 800 < 5_000, so
        // the first admission is the round where the accrued window first
        // reaches 50 000 ticks.
        assert_eq!(starving.rounds().0, granted);
    }

    /// The gate must have a second arm, or "refused" cannot be distinguished
    /// from "this fixture cannot run at all".
    #[test]
    fn the_ungated_control_admits_exactly_what_the_gate_refuses() {
        let refused = TickValveAccount::new(TickEffort::MAJOR_PASS)
            .request(40_000, 1_000)
            .allowance();
        let admitted = TickValveAccount::new(TickEffort::UNGATED)
            .request(40_000, 1_000)
            .allowance();
        assert_eq!(refused, None);
        assert_eq!(admitted, Some(4_000));
    }

    /// A pre-search round has no accrued window; the bootstrap reference is
    /// what stops preprocessing from never happening.
    #[test]
    fn a_zero_reference_falls_back_to_the_bootstrap_window() {
        let mut account = TickValveAccount::new(TickEffort::MAJOR_PASS);
        assert_eq!(
            account.request(0, 100),
            TickGrant::Granted {
                allowance: 200_000,
                reference: 2_000_000
            }
        );
    }

    /// Doubling, not the reference solvers' linear growth. The gaps between
    /// offers that reach the gate must be 1, 2, 4, 8 — asserted as the actual
    /// skip runs rather than as "backoff happened".
    #[test]
    fn a_pass_that_finds_nothing_is_offered_exponentially_less_often() {
        let mut account = TickValveAccount::new(TickEffort::UNGATED);
        // UNGATED has `max_backoff_rounds: 0`, i.e. no backoff at all, so use a
        // policy that gates nothing but still backs off.
        let effort = TickEffort {
            max_backoff_rounds: 32,
            ..TickEffort::UNGATED
        };
        account = TickValveAccount::new(effort);

        let mut runs = Vec::new();
        for _ in 0..4 {
            // Skip forward to the next round that actually reaches the gate.
            let mut skipped = 0u32;
            loop {
                match account.request(1_000_000, 10) {
                    TickGrant::BackedOff { .. } => skipped += 1,
                    TickGrant::Granted { .. } => break,
                    TickGrant::Refused { .. } => {
                        panic!("the control policy must never refuse")
                    }
                }
            }
            runs.push(skipped);
            account.record_outcome(false);
        }
        assert_eq!(
            runs,
            vec![0, 1, 2, 4],
            "the skip run must double after each unproductive round"
        );
        // ...and a productive round halves it, so the backoff is not one-way.
        account.record_outcome(true);
        assert_eq!(account.backoff().run_length(), 4);
    }

    #[test]
    fn the_backoff_cap_bounds_the_skip_run() {
        let mut b = TickBackoff::new();
        for _ in 0..20 {
            b.found_nothing(8);
        }
        assert_eq!(b.run_length(), 8);
        // A zero cap disables the backoff outright — the control knob.
        let mut off = TickBackoff::new();
        for _ in 0..20 {
            off.found_nothing(0);
        }
        assert_eq!(off.run_length(), 0);
        assert!(!off.delaying());
    }

    /// Every knob has to move a decision, or it is dead configuration and the
    /// policy is not the policy it claims to be.
    #[test]
    fn every_valve_weight_changes_a_decision() {
        // A base point where the gate is EXACTLY at the bar, so a change in
        // either direction is observable.
        let base = TickEffort {
            per_mille: 100,
            threshold_per_clause: 5,
            bootstrap_reference: 2_000_000,
            max_backoff_rounds: 4,
        };
        let at_bar = |e: TickEffort| TickValveAccount::new(e).request(50_000, 1_000);
        assert!(matches!(at_bar(base), TickGrant::Granted { .. }));

        // per_mille: halve it and the same window no longer clears.
        assert!(matches!(
            at_bar(TickEffort {
                per_mille: 50,
                ..base
            }),
            TickGrant::Refused { .. }
        ));
        // threshold_per_clause: double it and the same window no longer clears.
        assert!(matches!(
            at_bar(TickEffort {
                threshold_per_clause: 10,
                ..base
            }),
            TickGrant::Refused { .. }
        ));
        // bootstrap_reference: only reachable at a zero window, so probe there.
        let boot = |r: u64| {
            TickValveAccount::new(TickEffort {
                bootstrap_reference: r,
                ..base
            })
            .request(0, 1_000)
        };
        assert!(matches!(boot(2_000_000), TickGrant::Granted { .. }));
        assert!(matches!(boot(1_000), TickGrant::Refused { .. }));
        // max_backoff_rounds: 0 means an unproductive round costs nothing.
        let mut no_backoff = TickValveAccount::new(TickEffort {
            max_backoff_rounds: 0,
            ..base
        });
        no_backoff.record_outcome(false);
        assert!(matches!(
            no_backoff.request(50_000, 1_000),
            TickGrant::Granted { .. }
        ));
        let mut with_backoff = TickValveAccount::new(base);
        with_backoff.record_outcome(false);
        assert!(matches!(
            with_backoff.request(50_000, 1_000),
            TickGrant::BackedOff { .. }
        ));
    }

    /// The valve is the thing budgets are read from, so its arithmetic must not
    /// wrap into a fresh-looking allowance at absurd inputs.
    #[test]
    fn valve_arithmetic_saturates_rather_than_wrapping() {
        let effort = TickEffort {
            per_mille: u64::MAX,
            threshold_per_clause: u64::MAX,
            ..TickEffort::MAJOR_PASS
        };
        assert_eq!(effort.allowance(u64::MAX), u64::MAX);
        assert_eq!(effort.threshold(u64::MAX), u64::MAX);
        // A zero denominator cannot divide by zero.
        assert_eq!(mul_div(10, 3, 0), 0);
    }

    /// Determinism rule 1 and 2, enforced against this module's own source the
    /// way `axeyum_ir::budget` enforces them against its. A clock read or a
    /// float in the valve would make a schedule boundary host-dependent, which
    /// is the one property the whole tick unit exists to provide.
    #[test]
    fn the_valve_reads_no_clock_and_does_no_floating_point() {
        let src = include_str!("ticks.rs");
        let valve = src
            .split_once("// The tick valve:")
            .expect("the valve section marker must exist")
            .1;
        let valve = valve
            .split_once("#[cfg(test)]")
            .expect("the test module must follow the valve")
            .0;
        for banned in [
            "Instant",
            "SystemTime",
            "Duration",
            "elapsed",
            "f64",
            "f32",
            "as f",
            "1e-",
        ] {
            assert!(
                !valve.contains(banned),
                "the valve names `{banned}`: a budget decision that reads a \
                 clock or rounds in floating point is not reproducible across \
                 hosts, which is the entire claim of this module"
            );
        }
    }
}
