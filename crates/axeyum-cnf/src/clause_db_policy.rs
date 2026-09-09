//! Clause-database policy for the CDCL core: the *tier* scheme, its dynamic
//! boundaries, and the deletion ranking.
//!
//! This module exists so the reduce policy is a swappable object rather than a
//! set of constants inlined into the search loop. Everything the search asks of
//! it goes through [`ClauseDbPolicy`]; every tunable is a named field with a
//! documented default, and [`TierEstimator`] holds the one piece that is
//! genuinely *state* rather than configuration — the observed glue distribution
//! of clauses the search actually resolved through.
//!
//! # The tier scheme
//!
//! Learned clauses fall into three populations, decided by a *predicate on
//! glue* evaluated at reduce time. There is no per-tier list: a clause's tier
//! is derived from its current glue against the current boundaries, which is
//! what makes promotion (glue dropping on re-derivation) free.
//!
//! The lifetime signal is a small saturating counter set to
//! [`ClauseDbPolicy::max_used`] on learn and on every resolution, and
//! decremented once per reduce round. So the counter is *how many rounds of
//! disuse a clause has left*, and the three rules read it at different
//! thresholds:
//!
//! - **tier1** (`glue <= tier1`): kept while the counter is nonzero — i.e. used
//!   within the last `max_used` rounds. At the reference `max_used` of 31 that
//!   is a long lease, not a one-round one; it is the knob that decides how large
//!   the database grows.
//! - **tier2** (`tier1 < glue <= tier2`): kept only while the counter is still
//!   at `max_used - 1`, i.e. it was refreshed by a resolution and exactly one
//!   decrement has happened. One round of grace, then it is a candidate.
//! - **tier3** (`glue > tier2`): always a candidate, however recently used.
//!
//! Note what the counter is *not*: an exponentially-decayed activity score. An
//! activity score decays but never expires, so a clause resolved five times ten
//! thousand conflicts ago outranks one resolved twice last round. Neither
//! `CaDiCaL` nor Kissat consults clause activity anywhere in `reduce`.
//!
//! # Dynamic boundaries
//!
//! Fixed boundaries of 2 and 6 are the traditional choice, and they are wrong on
//! most formulas: average glue varies substantially between formulas and, in
//! solvers that alternate search modes, between modes on the *same* formula.
//! [`TierEstimator`] instead computes `tier1` as the smallest glue at which the
//! cumulative count of *used* clauses reaches 50%, and `tier2` as the smallest
//! reaching 90%, recomputed on a doubling conflict interval. Until anything has
//! been used it reports the 2/6 fallback.
//!
//! This matters here specifically because we mostly solve bit-blasted formulas,
//! whose glue profile is not the combinatorial-benchmark profile that 2/6 was
//! chosen against, and nobody has ever tuned those constants for it.
//!
//! # Determinism
//!
//! Percentiles are computed in integer per-mille arithmetic, not floating point,
//! so the boundaries are bit-reproducible across platforms. The deletion
//! fraction uses `f64::log10`, which is the one place this module touches
//! floating point; it mirrors the reference's ramp and is deterministic under
//! IEEE-754.
//!
//! # Source
//!
//! The mechanism, the constants, and the rationale are documented against
//! Kissat 4.0.4 and `CaDiCaL` in
//! `docs/research/02-ecosystems/pipeline-survey-2026-09/cdcl-core-engine.md`
//! (findings R1 and R2).

/// Saturating maximum of a clause's `used` counter. Written on learn and on
/// every resolution, decremented once per reduce round, so a clause that is
/// still at `MAX_USED - 1` at reduce time was resolved since the previous
/// round. Both references use 31 (a 5-bit field).
pub const MAX_USED: u8 = 31;

/// The `used` value a tier2 clause must still carry to survive a round when
/// [`ClauseDbPolicy::max_used`] is the reference [`MAX_USED`]: it was set by a
/// resolution and decremented exactly once by the current round. This is the
/// "one round of grace" boundary. A policy with a different `max_used` derives
/// its own grace value from that field.
pub const TIER2_GRACE_USED: u8 = MAX_USED - 1;

/// Largest glue tracked in the used-glue histogram. Clauses above this are
/// counted in the final bucket; they are deep in tier3 either way, so the
/// truncation cannot move a boundary that any clause is near.
pub const MAX_GLUE_USED: u32 = 127;

/// Which population a clause belongs to, derived from its glue and the current
/// boundaries. Reported for instrumentation as well as consumed by the keep
/// rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tier {
    /// `glue <= tier1`: the core, kept while it is used at all.
    One,
    /// `tier1 < glue <= tier2`: kept for one round after its last use.
    Two,
    /// `glue > tier2`: always a deletion candidate.
    Three,
}

/// Why a clause survived (or did not survive) a reduce round. Every reduce
/// decision resolves to exactly one of these, which is what lets the counters
/// account for the whole population rather than only the deletions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KeepReason {
    /// The clause is the reason for a currently-assigned literal. Deleting it
    /// would corrupt the implication graph.
    Locked,
    /// Tier1 and used since the last round.
    Tier1Used,
    /// Tier2 and used since the last round (one round of grace).
    Tier2Recent,
    /// Below the legacy permanent-glue boundary (only under
    /// [`KeepRule::GluePermanent`]).
    PermanentGlue,
    /// Too short to be worth deleting (binary and unit clauses are never
    /// candidates in either reference).
    TooShort,
    /// None of the above: the clause is a deletion candidate this round.
    Candidate,
}

/// The keep predicate: which clauses are exempt from deletion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KeepRule {
    /// The tier scheme described in the module docs. This is the default.
    Tiers,
    /// The pre-2026-09 rule kept for A/B measurement: a clause with
    /// `glue <= glue_limit` is immortal regardless of whether it is ever used
    /// again, and everything else is a candidate. Retained as a selectable
    /// policy so a change to the tier scheme can be measured against the
    /// baseline it replaced without reverting code.
    GluePermanent {
        /// Glue at or below which a clause is never deleted.
        glue_limit: u32,
    },
}

/// The deletion ranking key. Candidates are sorted ascending by this and the
/// prefix is deleted, so a *smaller* key means "delete this first".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RankKey {
    /// Descending glue, then descending size: the worst clause is the one with
    /// the most decision levels, and among those the longest. This is what both
    /// references use, and neither consults clause activity at all. Default.
    GlueThenSize,
    /// Ascending clause activity (an exponentially-decayed count of the
    /// clause's participation in conflicts). The pre-2026-09 ranking, kept
    /// selectable for A/B measurement.
    Activity,
}

/// How large a share of the candidate set a round deletes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeleteFraction {
    /// A fixed share, in per mille. `Fixed { permille: 500 }` is the
    /// pre-2026-09 "delete the worst half".
    Fixed {
        /// Share of candidates deleted, per mille.
        permille: u32,
    },
    /// Kissat's ramp: `high - (high - low) / log10(round + 9)`, so the first
    /// round deletes `low` and the share climbs asymptotically toward `high`.
    /// Early rounds are conservative because the database is small and every
    /// clause is recent; later rounds are aggressive because it is not.
    /// Default is `low` = 500, `high` = 900 per mille.
    Ramped {
        /// Share deleted on the first round, per mille.
        low_permille: u32,
        /// Asymptotic share, per mille.
        high_permille: u32,
    },
}

/// How a reduce round restores the watch lists after tombstoning its
/// deletions.
///
/// Both alternatives leave the **same set** of watches: `propagate` keeps a
/// long clause's two watched literals at arena slots 0 and 1, and a binary
/// clause's two literals are both watched, so re-watching "the first two
/// literals of every live clause" re-derives exactly what was already there.
/// What differs is the cost and the **order within each list**, and the order
/// is visible to the search: it decides which of several unit clauses
/// propagates first and therefore which conflict is analysed.
///
/// # Why the expensive one is still the default
///
/// [`WatchSweep::InPlace`] is the reference behaviour and is strictly cheaper,
/// and it is **not** the default here, because measurement on this repository's
/// corpus said the trade does not pay:
///
/// * The sweep is not a cost worth optimising. Measured 2026-09-08 over the
///   committed van der Waerden / Rado instances and generated bit-blasted
///   factorisation instances, the watch entries a reduce round touches are
///   **0.3%–2.8% of the watch entries propagation visits** (median under 0.8%).
///   Removing the sweep entirely would not reach 1%.
/// * Order is not free. Over the eight corpus instances that reduce at all,
///   `InPlace` needed **more** conflicts on seven — +1.3% to +6.3% — and fewer
///   on one (-2.3%). There is a mechanism for it: a rebuild leaves every list
///   in clause-id order, which puts the short input clauses ahead of the long
///   learned ones, and it refreshes each blocker to the clause's actual other
///   watched literal instead of whatever `propagate` last cached.
///
/// Seven of eight is suggestive, not conclusive (n = 8), which is exactly why
/// this is a selectable policy with both arms measurable rather than a decision
/// welded into the search. What is *not* in doubt is the denominator: whichever
/// sweep wins, it is worth less than 1% of propagation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WatchSweep {
    /// Clear all `2n` lists and re-push a pair per live clause, reading
    /// `headers[cid]` and two arena cells for each. Walks the whole database
    /// including input clauses, which are never deletable, and leaves every
    /// list in clause-id order. The pre-2026-09 behaviour, and still the
    /// default — see the type docs for the measurement.
    Rebuild,
    /// Retain in place: drop only the watches pointing at a clause this round
    /// tombstoned. Touches no header and no arena cell, allocates nothing, and
    /// preserves each list's existing order. The reference behaviour
    /// (Kissat `reduce.c:161,183`).
    InPlace,
}

/// When a reduce round fires.
///
/// This is not an independent knob: the trigger and the keep rule interact, and
/// picking them separately is how the first tier implementation here lost 2x in
/// throughput while winning 20% in conflicts.
///
/// The tier rule's protection is "used since the *previous round*", so its
/// selectivity is a function of how far apart rounds are. Pair it with a
/// database-size trigger and the two fight: protection keeps the database above
/// the size threshold, which fires the next round sooner, which shortens the
/// window, which protects more. Measured on `vdw-2-3-11`, the size trigger fired
/// 126 rounds under the tier rule against 76 under the legacy rule, on a run
/// that analysed *fewer* conflicts — and each round rebuilds every watch list.
/// A conflict-interval trigger breaks the loop because the window does not
/// depend on what the last round kept.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReduceSchedule {
    /// Reduce when the live learned-clause count exceeds `first + inc * rounds`.
    /// The pre-2026-09 trigger (a `MiniSat`/Glucose database-size budget), kept
    /// selectable for A/B measurement.
    LearnedBudget {
        /// Clauses tolerated before the first round.
        first: usize,
        /// Additive growth of the budget after each round.
        inc: usize,
    },
    /// Reduce `init` conflicts after the search starts and `interval *
    /// sqrt(rounds)` conflicts after each round — the reference schedule, so
    /// rounds get further apart as the search goes on. Default, with `init` and
    /// `interval` both 1000 (Kissat's `reduceinit` / `reduceint`).
    ConflictInterval {
        /// Conflicts before the first round.
        init: u64,
        /// Scale of the inter-round interval.
        interval: u64,
    },
}

/// Tunables for [`TierEstimator`]. Defaults mirror Kissat 4.0.4.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TierConfig {
    /// Cumulative share of used clauses that defines `tier1`, per mille.
    /// Default 500: a clause with glue up to `tier1` has roughly a 50% chance
    /// of being used.
    pub tier1_permille: u64,
    /// Cumulative share that defines `tier2`, per mille. Default 900: clauses
    /// above `tier2` have under a 10% chance of being used.
    pub tier2_permille: u64,
    /// `tier1` reported before anything has been used. Default 2.
    pub tier1_fallback: u32,
    /// `tier2` reported before anything has been used. Default 6.
    pub tier2_fallback: u32,
    /// Conflicts before the first recomputation. Default 2 — the estimate is
    /// worthless that early, but it costs a 128-entry scan and starting small
    /// is what makes the doubling schedule cheap to reason about.
    pub initial_interval: u64,
    /// Ceiling on the doubling interval. Default 65536 conflicts.
    pub max_interval: u64,
}

impl Default for TierConfig {
    fn default() -> Self {
        Self {
            tier1_permille: 500,
            tier2_permille: 900,
            tier1_fallback: 2,
            tier2_fallback: 6,
            initial_interval: 2,
            max_interval: 1 << 16,
        }
    }
}

/// The observed glue distribution of clauses the search resolved through, and
/// the tier boundaries derived from it.
///
/// This is *state*, not configuration: it is fed by
/// [`TierEstimator::on_clause_used`] at every resolution and re-derives its
/// boundaries on a doubling conflict schedule. Keeping it separate from
/// [`ClauseDbPolicy`]'s configuration is what lets a fixed-boundary policy and a
/// percentile policy coexist behind one object.
///
/// The histogram is cumulative over the whole search and is never reset, which
/// is the reference behaviour: the boundaries should describe the formula, and
/// resetting would make them describe only the most recent interval.
///
/// The references keep one histogram *per search mode* (stable / focused),
/// because glue profiles differ between modes on the same formula. We have no
/// mode switching yet, so this is the degenerate one-mode case; a future mode
/// switch wants an array of these indexed by mode, not a reset.
#[derive(Debug, Clone)]
pub struct TierEstimator {
    cfg: TierConfig,
    /// `used_glue[g]` = number of resolutions through a clause whose glue was
    /// `g` (saturating at [`MAX_GLUE_USED`]).
    used_glue: Vec<u64>,
    total_used: u64,
    tier1: u32,
    tier2: u32,
    interval: u64,
    next_conflicts: u64,
    recomputes: u64,
}

impl Default for TierEstimator {
    fn default() -> Self {
        Self::new(TierConfig::default())
    }
}

impl TierEstimator {
    /// A fresh estimator reporting the configured fallback boundaries.
    #[must_use]
    pub fn new(cfg: TierConfig) -> Self {
        Self {
            used_glue: vec![0; MAX_GLUE_USED as usize + 1],
            total_used: 0,
            tier1: cfg.tier1_fallback,
            tier2: cfg.tier2_fallback,
            interval: cfg.initial_interval,
            next_conflicts: cfg.initial_interval,
            recomputes: 0,
            cfg,
        }
    }

    /// Records one resolution through a clause of this glue.
    pub fn on_clause_used(&mut self, glue: u32) {
        let bucket = glue.min(MAX_GLUE_USED) as usize;
        self.used_glue[bucket] += 1;
        self.total_used += 1;
    }

    /// Recomputes the boundaries if the conflict schedule is due, and returns
    /// whether it did. Call once per conflict.
    pub fn maybe_recompute(&mut self, conflicts: u64) -> bool {
        if conflicts < self.next_conflicts {
            return false;
        }
        self.recompute();
        if self.interval < self.cfg.max_interval {
            self.interval = (self.interval * 2).min(self.cfg.max_interval);
        }
        self.next_conflicts = conflicts.saturating_add(self.interval);
        true
    }

    /// Recomputes the boundaries from the current histogram, unconditionally.
    pub fn recompute(&mut self) {
        self.recomputes += 1;
        if self.total_used == 0 {
            self.tier1 = self.cfg.tier1_fallback;
            self.tier2 = self.cfg.tier2_fallback;
            return;
        }
        // Integer per-mille percentiles: deterministic across platforms in a
        // way `total as f64 * 0.5` is not. Both limits are floored at 1 so a
        // one-sample histogram cannot produce a boundary of 0 (which would put
        // every clause in tier3 and delete the database).
        let limit1 = (self.total_used * self.cfg.tier1_permille / 1000).max(1);
        let limit2 = (self.total_used * self.cfg.tier2_permille / 1000).max(1);
        let mut accumulated = 0u64;
        let mut found1: Option<u32> = None;
        let mut found2: Option<u32> = None;
        for (glue, count) in self.used_glue.iter().enumerate() {
            accumulated += count;
            #[allow(clippy::cast_possible_truncation)]
            let glue = glue as u32;
            if found1.is_none() && accumulated >= limit1 {
                found1 = Some(glue);
            }
            if accumulated >= limit2 {
                found2 = Some(glue);
                break;
            }
        }
        self.tier1 = found1.unwrap_or(self.cfg.tier1_fallback);
        // `tier2 >= tier1` is an invariant of the tier semantics, not an
        // accident of the histogram: tier2 is a *wider* band than tier1. It can
        // only be violated by a degenerate histogram (a single glue bucket
        // carrying both percentiles), in which case tier2 collapses onto tier1
        // and the middle band is empty, which is correct.
        self.tier2 = found2.unwrap_or(self.cfg.tier2_fallback).max(self.tier1);
    }

    /// The current `(tier1, tier2)` boundaries.
    #[must_use]
    pub fn limits(&self) -> (u32, u32) {
        (self.tier1, self.tier2)
    }

    /// How many times the boundaries have been recomputed.
    #[must_use]
    pub fn recomputes(&self) -> u64 {
        self.recomputes
    }

    /// Total resolutions recorded.
    #[must_use]
    pub fn total_used(&self) -> u64 {
        self.total_used
    }

    /// The population a clause with this glue currently belongs to.
    #[must_use]
    pub fn tier_of(&self, glue: u32) -> Tier {
        if glue <= self.tier1 {
            Tier::One
        } else if glue <= self.tier2 {
            Tier::Two
        } else {
            Tier::Three
        }
    }
}

/// The reduce-round policy: what to keep, how to rank what is left, and how much
/// of it to delete.
///
/// The search owns one of these and never inlines a decision it can ask for.
/// Swapping [`ClauseDbPolicy::legacy`] for [`ClauseDbPolicy::default`] changes
/// the clause-database behaviour completely without touching the search loop.
#[derive(Debug, Clone)]
pub struct ClauseDbPolicy {
    /// Which clauses are exempt from deletion.
    pub keep_rule: KeepRule,
    /// How the surviving candidates are ordered for deletion.
    pub rank_key: RankKey,
    /// What share of candidates a round deletes.
    pub fraction: DeleteFraction,
    /// When a round fires. Coupled to `keep_rule`; see [`ReduceSchedule`].
    pub schedule: ReduceSchedule,
    /// Clauses at or below this length are never candidates. Default 2: neither
    /// reference deletes binary clauses, and our watch scheme relies on binaries
    /// staying resident.
    pub min_deletable_len: usize,
    /// Value written into a clause's lifetime counter when it is learned or
    /// resolved. Since the counter is decremented once per reduce round, this is
    /// **how many reduce rounds a tier1 clause survives after its last use**.
    ///
    /// [`MAX_USED`] (31) is the reference value and is deliberately generous.
    /// It is exposed because it is the single knob that trades search quality
    /// against database size, and the trade lands differently for us than for
    /// the references: they run vivification, subsumption and variable
    /// elimination that shrink the database between rounds, and they special-case
    /// binary clauses out of the watch lists. We do neither, so a database the
    /// reference tolerates costs us proportionally more watch traffic. Measured
    /// on `vdw-2-3-11`: at 31 the tier policy holds 2.4x the live learned
    /// clauses and examines 2x the watch entries per conflict.
    ///
    /// Must be at least 1; 1 means "survives only the round it was used in".
    ///
    /// # The curve, measured
    ///
    /// Swept 2026-09-08 against the pre-2026-09 database over the seven corpus
    /// instances that decide and reduce (geometric means; the full method and
    /// the fixed-work half are in
    /// `docs/research/12-performance/max-used-curve-2026-09-08.md`):
    ///
    /// | `max_used` | conflicts | watch visits | ticks |
    /// | --- | ---: | ---: | ---: |
    /// | 31 | 0.860 | 1.254 | 1.088 |
    /// | 8 | **0.851** | 1.210 | 1.070 |
    /// | 2 | 0.880 | 1.151 | 1.046 |
    /// | 1 | 0.879 | **1.003** | **0.954** |
    ///
    /// Two things that are not obvious from the value alone:
    ///
    /// * **The conflict column is non-monotone and 31 is not its optimum** — it
    ///   improves down to 8 and degrades below that. The reference value is not
    ///   the best setting even for the metric the tier policy exists to improve.
    /// * **`max_used = 1` is a different policy, not the end of a slide.** The
    ///   tier2 grace is floored at `max(max_used - 1, 1)` and tier1 keeps on
    ///   `used_before > 0`, so at 1 the two predicates coincide and tier1/tier2
    ///   **collapse into a single rule**: keep if `glue <= tier2` and the clause
    ///   was resolved since the previous round. That is why the watch-visit
    ///   column steps rather than slides there.
    ///
    /// The default stays at the reference 31 because the corpus is seven
    /// instances, five of them combinatorial, and on the one genuinely hard
    /// bit-blasted instance the curve runs the *other* way (8 best, 1 worse
    /// than 31). 1 and 8 are the two candidates a wider corpus should decide
    /// between.
    pub max_used: u8,
    /// Whether to recompute a clause's glue when it is resolved and lower it if
    /// the new value is smaller (promotion). Never raises glue: there is no
    /// demotion in either reference, because a clause that was once
    /// level-compact earned its place.
    pub promote_on_use: bool,
    /// Conflicts to wait after a round that deleted nothing before attempting
    /// another. Without this a fully-protected database makes the size-triggered
    /// reduce fire on every conflict and scan the whole clause list each time.
    /// Default 300, matching the learned-budget growth step.
    pub empty_round_backoff: u64,
    /// How a reduce round restores the watch lists after its deletions.
    pub watch_sweep: WatchSweep,
    /// The dynamic tier boundaries. State, not configuration.
    pub tiers: TierEstimator,
}

impl Default for ClauseDbPolicy {
    fn default() -> Self {
        Self::tiered()
    }
}

impl ClauseDbPolicy {
    /// The tier policy: three-tier lifetime keyed on a `used` counter, dynamic
    /// boundaries, glue-then-size ranking, ramped deletion fraction.
    #[must_use]
    pub fn tiered() -> Self {
        Self {
            keep_rule: KeepRule::Tiers,
            rank_key: RankKey::GlueThenSize,
            fraction: DeleteFraction::Ramped {
                low_permille: 500,
                high_permille: 900,
            },
            schedule: ReduceSchedule::ConflictInterval {
                init: 1_000,
                interval: 1_000,
            },
            max_used: MAX_USED,
            min_deletable_len: 2,
            promote_on_use: true,
            empty_round_backoff: 300,
            watch_sweep: WatchSweep::Rebuild,
            tiers: TierEstimator::default(),
        }
    }

    /// The pre-2026-09 policy, for A/B measurement: glue &le; 2 immortal,
    /// activity ranking, delete the worst half. The tier estimator is still fed
    /// (so its instrumentation is comparable) but nothing consults it.
    #[must_use]
    pub fn legacy() -> Self {
        Self {
            keep_rule: KeepRule::GluePermanent { glue_limit: 2 },
            rank_key: RankKey::Activity,
            fraction: DeleteFraction::Fixed { permille: 500 },
            schedule: ReduceSchedule::LearnedBudget {
                first: 2_000,
                inc: 300,
            },
            max_used: MAX_USED,
            min_deletable_len: 2,
            promote_on_use: false,
            empty_round_backoff: 300,
            watch_sweep: WatchSweep::Rebuild,
            tiers: TierEstimator::default(),
        }
    }

    /// Records one resolution through a clause of this glue, feeding the tier
    /// estimator's histogram.
    pub fn on_clause_used(&mut self, glue: u32) {
        self.tiers.on_clause_used(glue);
    }

    /// Per-conflict tick: lets the tier estimator recompute on schedule.
    /// Returns whether it did.
    pub fn on_conflict(&mut self, conflicts: u64) -> bool {
        self.tiers.maybe_recompute(conflicts)
    }

    /// The population a clause with this glue currently belongs to. Meaningful
    /// under any keep rule; under [`KeepRule::GluePermanent`] it is
    /// instrumentation only.
    #[must_use]
    pub fn tier_of(&self, glue: u32) -> Tier {
        self.tiers.tier_of(glue)
    }

    /// The reduce decision for one live learned clause.
    ///
    /// `used_before` is the counter's value *before* this round's decrement, so
    /// `used_before > 0` means "resolved since the previous round" and
    /// `used_before >= max_used - 1` means "resolved since the previous round
    /// and not yet decremented past its grace".
    #[must_use]
    pub fn classify(&self, glue: u32, size: usize, used_before: u8, locked: bool) -> KeepReason {
        if locked {
            return KeepReason::Locked;
        }
        if size <= self.min_deletable_len {
            return KeepReason::TooShort;
        }
        match self.keep_rule {
            KeepRule::GluePermanent { glue_limit } => {
                if glue <= glue_limit {
                    KeepReason::PermanentGlue
                } else {
                    KeepReason::Candidate
                }
            }
            KeepRule::Tiers => {
                let (tier1, tier2) = self.tiers.limits();
                // `used_before` is the value BEFORE this round's decrement, so
                // `> 0` means "used within the last `max_used` rounds" and
                // `>= max_used - 1` means "used since the previous round".
                // Floored at 1: with `max_used == 1` a grace of 0 would make
                // `used_before >= grace` vacuously true and tier2 would keep the
                // entire database. Measured: that grew the live learned set 2.7x
                // beyond even the reference setting.
                let grace = self.max_used.saturating_sub(1).max(1);
                if glue <= tier1 && used_before > 0 {
                    KeepReason::Tier1Used
                } else if glue <= tier2 && used_before >= grace {
                    KeepReason::Tier2Recent
                } else {
                    KeepReason::Candidate
                }
            }
        }
    }

    /// Sort key for a deletion candidate. Candidates are sorted ascending and
    /// the prefix deleted, so a smaller key is a worse clause.
    ///
    /// Under [`RankKey::GlueThenSize`] this packs the bitwise complement of glue
    /// into the high half and of size into the low half, so ascending order is
    /// descending glue then descending size. Under [`RankKey::Activity`] it is
    /// the activity's IEEE-754 bit pattern, which is monotone in the value for
    /// the non-negative finite activities the search produces.
    #[must_use]
    pub fn rank(&self, glue: u32, size: usize, activity: f64) -> u64 {
        match self.rank_key {
            RankKey::GlueThenSize => {
                #[allow(clippy::cast_possible_truncation)]
                let size = size.min(u32::MAX as usize) as u32;
                (u64::from(!glue) << 32) | u64::from(!size)
            }
            RankKey::Activity => {
                // Non-negative and finite by construction (bumped by a positive
                // increment from 0.0, rescaled by a positive factor), so the
                // bit pattern orders exactly as the value does.
                debug_assert!(activity >= 0.0 && activity.is_finite());
                activity.to_bits()
            }
        }
    }

    /// Is a reduce round due?
    ///
    /// `rounds` is how many have already run; `next_conflict_limit` is the value
    /// [`ClauseDbPolicy::next_reduce_limit`] returned after the last one (0
    /// before any). Under [`ReduceSchedule::LearnedBudget`] the conflict count
    /// is ignored; under [`ReduceSchedule::ConflictInterval`] the database size
    /// is.
    #[must_use]
    pub fn reduce_due(
        &self,
        learned_live: usize,
        conflicts: u64,
        rounds: u64,
        next_conflict_limit: u64,
    ) -> bool {
        match self.schedule {
            ReduceSchedule::LearnedBudget { first, inc } => {
                #[allow(clippy::cast_possible_truncation)]
                let budget = first.saturating_add(inc.saturating_mul(rounds as usize));
                learned_live > budget
            }
            ReduceSchedule::ConflictInterval { .. } => conflicts >= next_conflict_limit,
        }
    }

    /// The conflict count at which the next round is due, given that `rounds`
    /// have now run. Meaningless (and zero) under
    /// [`ReduceSchedule::LearnedBudget`].
    #[must_use]
    pub fn next_reduce_limit(&self, conflicts: u64, rounds: u64) -> u64 {
        match self.schedule {
            ReduceSchedule::LearnedBudget { .. } => 0,
            ReduceSchedule::ConflictInterval { init, interval } => {
                if rounds == 0 {
                    return conflicts.saturating_add(init);
                }
                #[allow(clippy::cast_precision_loss)]
                let scaled = (interval as f64) * (rounds as f64).sqrt();
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let delta = (scaled as u64).max(1);
                conflicts.saturating_add(delta)
            }
        }
    }

    /// How many of `candidates` this round deletes. `round` is 1-based.
    #[must_use]
    pub fn delete_count(&self, candidates: usize, round: u64) -> usize {
        let permille = match self.fraction {
            DeleteFraction::Fixed { permille } => u64::from(permille),
            DeleteFraction::Ramped {
                low_permille,
                high_permille,
            } => {
                let low = f64::from(low_permille);
                let high = f64::from(high_permille);
                // `log10(round + 9)` is 1 at round 1, so the first round is
                // exactly `low` and the share climbs toward `high`.
                #[allow(clippy::cast_precision_loss)]
                let denominator = ((round as f64) + 9.0).log10();
                let value = if denominator > 0.0 {
                    high - (high - low) / denominator
                } else {
                    low
                };
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                {
                    value.clamp(low, high) as u64
                }
            }
        };
        let count = (candidates as u64) * permille / 1000;
        #[allow(clippy::cast_possible_truncation)]
        {
            (count as usize).min(candidates)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fallback_limits_hold_until_something_is_used() {
        let mut est = TierEstimator::default();
        assert_eq!(est.limits(), (2, 6));
        assert!(est.maybe_recompute(2), "the first interval is 2 conflicts");
        assert_eq!(
            est.limits(),
            (2, 6),
            "an empty histogram must report the fallback, not 0/0"
        );
    }

    #[test]
    fn percentiles_track_the_used_glue_distribution() {
        let mut est = TierEstimator::default();
        // 60 clauses at glue 4, 35 at glue 9, 5 at glue 40.
        for _ in 0..60 {
            est.on_clause_used(4);
        }
        for _ in 0..35 {
            est.on_clause_used(9);
        }
        for _ in 0..5 {
            est.on_clause_used(40);
        }
        est.recompute();
        // 50% of 100 is 50, reached inside the glue-4 bucket.
        // 90% is 90, reached inside the glue-9 bucket.
        assert_eq!(est.limits(), (4, 9));
        assert_eq!(est.tier_of(3), Tier::One);
        assert_eq!(est.tier_of(4), Tier::One);
        assert_eq!(est.tier_of(5), Tier::Two);
        assert_eq!(est.tier_of(9), Tier::Two);
        assert_eq!(est.tier_of(10), Tier::Three);
    }

    #[test]
    fn boundaries_move_when_the_distribution_does() {
        // The whole point of R2: a formula whose useful clauses are glue 12
        // must not be scored against a hard-coded boundary of 2.
        let mut est = TierEstimator::default();
        for _ in 0..100 {
            est.on_clause_used(12);
        }
        est.recompute();
        assert_eq!(
            est.limits(),
            (12, 12),
            "a single-bucket distribution collapses both boundaries onto it"
        );
        assert_eq!(est.tier_of(12), Tier::One);
        assert_eq!(est.tier_of(13), Tier::Three);
    }

    #[test]
    fn glue_above_the_histogram_bound_is_counted_in_the_last_bucket() {
        let mut est = TierEstimator::default();
        est.on_clause_used(10_000);
        est.recompute();
        assert_eq!(est.limits(), (MAX_GLUE_USED, MAX_GLUE_USED));
        assert_eq!(est.total_used(), 1);
    }

    #[test]
    fn recompute_interval_doubles_and_caps() {
        let cfg = TierConfig::default();
        let mut est = TierEstimator::new(cfg);
        let mut conflicts = 0u64;
        let mut fired = 0u64;
        // Walk far enough that the interval must have saturated at max_interval.
        while conflicts < 4 * cfg.max_interval {
            conflicts += 1;
            if est.maybe_recompute(conflicts) {
                fired += 1;
            }
        }
        assert_eq!(fired, est.recomputes());
        // Doubling from 2 to 65536 is 16 steps; the remaining ~3 * 65536
        // conflicts contribute 3 more. Anything near a per-conflict recompute
        // would be orders of magnitude larger.
        assert!(
            (16..=24).contains(&fired),
            "doubling schedule fired {fired} times, expected ~19"
        );
    }

    #[test]
    fn tier1_keeps_a_used_clause_and_drops_a_cold_one() {
        let mut policy = ClauseDbPolicy::tiered();
        for _ in 0..100 {
            policy.on_clause_used(3);
        }
        policy.tiers.recompute();
        assert_eq!(policy.tiers.limits(), (3, 3));
        assert_eq!(
            policy.classify(3, 10, 1, false),
            KeepReason::Tier1Used,
            "tier1 survives on any use at all"
        );
        assert_eq!(
            policy.classify(3, 10, 0, false),
            KeepReason::Candidate,
            "tier1 that went cold for a round is a candidate"
        );
    }

    #[test]
    fn tier2_gets_exactly_one_round_of_grace() {
        let mut policy = ClauseDbPolicy::tiered();
        for _ in 0..50 {
            policy.on_clause_used(2);
        }
        for _ in 0..50 {
            policy.on_clause_used(8);
        }
        policy.tiers.recompute();
        let (tier1, tier2) = policy.tiers.limits();
        assert_eq!((tier1, tier2), (2, 8));
        assert_eq!(
            policy.classify(5, 10, TIER2_GRACE_USED, false),
            KeepReason::Tier2Recent,
            "resolved since the last round"
        );
        assert_eq!(
            policy.classify(5, 10, TIER2_GRACE_USED - 1, false),
            KeepReason::Candidate,
            "one further round without a resolution and the grace is spent"
        );
    }

    #[test]
    fn a_max_used_of_one_does_not_make_tier2_keep_everything() {
        // Degenerate case found by measurement, not by reading: with
        // `max_used == 1` the grace threshold `max_used - 1` is 0, and
        // `used_before >= 0` is vacuously true, so tier2 would keep the whole
        // database. On `vdw-2-3-11` that grew the live learned set to 86,528
        // clauses against 31,864 at the reference setting -- the opposite of
        // what shortening the lifetime is supposed to do.
        let mut policy = ClauseDbPolicy::tiered();
        policy.max_used = 1;
        for _ in 0..50 {
            policy.on_clause_used(2);
        }
        for _ in 0..50 {
            policy.on_clause_used(8);
        }
        policy.tiers.recompute();
        assert_eq!(policy.tiers.limits(), (2, 8));
        assert_eq!(
            policy.classify(5, 10, 0, false),
            KeepReason::Candidate,
            "a cold tier2 clause must be a candidate at every `max_used`"
        );
        assert_eq!(
            policy.classify(5, 10, 1, false),
            KeepReason::Tier2Recent,
            "and a clause used since the last round must still be kept"
        );
    }

    #[test]
    fn max_used_sets_how_many_rounds_a_tier1_clause_survives() {
        // The knob's whole meaning: a tier1 clause is kept while its counter is
        // nonzero, and the counter starts at `max_used` and drops once a round.
        for max_used in [1u8, 4, 31] {
            let mut policy = ClauseDbPolicy::tiered();
            policy.max_used = max_used;
            for _ in 0..100 {
                policy.on_clause_used(3);
            }
            policy.tiers.recompute();
            let mut used = max_used;
            let mut survived = 0;
            // Simulate rounds with no further use: decrement, then classify on
            // the PRE-decrement value, exactly as `reduce_db` does.
            while policy.classify(3, 10, used, false) != KeepReason::Candidate {
                survived += 1;
                used = used.saturating_sub(1);
                assert!(survived <= 64, "tier1 clause never became a candidate");
            }
            assert_eq!(
                survived,
                u32::from(max_used),
                "max_used={max_used} should buy exactly that many rounds"
            );
        }
    }

    #[test]
    fn tier3_is_always_a_candidate_however_recently_used() {
        let mut policy = ClauseDbPolicy::tiered();
        for _ in 0..100 {
            policy.on_clause_used(2);
        }
        policy.tiers.recompute();
        assert_eq!(
            policy.classify(50, 30, MAX_USED, false),
            KeepReason::Candidate
        );
    }

    #[test]
    fn locked_and_short_clauses_are_never_candidates() {
        let policy = ClauseDbPolicy::tiered();
        assert_eq!(policy.classify(40, 30, 0, true), KeepReason::Locked);
        assert_eq!(policy.classify(40, 2, 0, false), KeepReason::TooShort);
    }

    #[test]
    fn legacy_policy_reproduces_the_permanent_glue_rule() {
        let policy = ClauseDbPolicy::legacy();
        assert_eq!(policy.classify(2, 10, 0, false), KeepReason::PermanentGlue);
        assert_eq!(
            policy.classify(3, 10, MAX_USED, false),
            KeepReason::Candidate,
            "the legacy rule ignores use entirely"
        );
    }

    #[test]
    fn glue_then_size_ranks_worst_first() {
        let policy = ClauseDbPolicy::tiered();
        let high_glue = policy.rank(40, 10, 0.0);
        let low_glue = policy.rank(3, 10, 0.0);
        assert!(
            high_glue < low_glue,
            "higher glue must sort earlier (deleted first)"
        );
        let long = policy.rank(10, 90, 0.0);
        let short = policy.rank(10, 5, 0.0);
        assert!(
            long < short,
            "at equal glue, the longer clause is deleted first"
        );
        assert!(
            policy.rank(40, 5, 0.0) < policy.rank(39, 90, 0.0),
            "glue dominates size"
        );
    }

    #[test]
    fn activity_ranking_orders_by_value() {
        let policy = ClauseDbPolicy::legacy();
        assert!(policy.rank(1, 1, 0.0) < policy.rank(1, 1, 1e-30));
        assert!(policy.rank(1, 1, 1e-30) < policy.rank(1, 1, 1.0));
        assert!(policy.rank(1, 1, 1.0) < policy.rank(1, 1, 1e19));
    }

    #[test]
    fn the_conflict_interval_schedule_spreads_rounds_out() {
        let policy = ClauseDbPolicy::tiered();
        // First round at `init`, then `interval * sqrt(rounds)` past each.
        assert_eq!(policy.next_reduce_limit(0, 0), 1_000);
        assert_eq!(policy.next_reduce_limit(1_000, 1), 2_000);
        assert_eq!(policy.next_reduce_limit(2_000, 4), 4_000);
        assert_eq!(policy.next_reduce_limit(10_000, 100), 20_000);
        // And it does not read the database size at all -- which is the whole
        // point, because the tier rule's selectivity depends on how far apart
        // rounds are, so a size-driven trigger feeds back on itself.
        assert!(policy.reduce_due(0, 1_000, 0, 1_000));
        assert!(!policy.reduce_due(usize::MAX, 999, 0, 1_000));
    }

    #[test]
    fn the_learned_budget_schedule_reads_the_database_and_not_the_clock() {
        let policy = ClauseDbPolicy::legacy();
        assert_eq!(
            policy.next_reduce_limit(12_345, 7),
            0,
            "the budget schedule has no conflict limit to report"
        );
        assert!(
            !policy.reduce_due(2_000, u64::MAX, 0, 0),
            "2000 is not > 2000"
        );
        assert!(policy.reduce_due(2_001, 0, 0, 0));
        // The budget grows by `inc` per round.
        assert!(!policy.reduce_due(2_300, 0, 1, 0));
        assert!(policy.reduce_due(2_301, 0, 1, 0));
    }

    #[test]
    fn the_two_schedules_disagree_on_the_same_state() {
        // A discriminating state: a large database very early in the search.
        // The budget schedule fires; the interval schedule does not. If both
        // gave the same answer the selector would be decoration.
        let interval = ClauseDbPolicy::tiered();
        let budget = ClauseDbPolicy::legacy();
        let (live, conflicts, rounds) = (50_000usize, 10u64, 0u64);
        assert!(budget.reduce_due(live, conflicts, rounds, 0));
        assert!(!interval.reduce_due(live, conflicts, rounds, 1_000));
    }

    #[test]
    fn ramped_fraction_starts_at_low_and_climbs_toward_high() {
        let policy = ClauseDbPolicy::tiered();
        assert_eq!(policy.delete_count(1000, 1), 500);
        let round_91 = policy.delete_count(1000, 91);
        assert!(
            (690..=710).contains(&round_91),
            "round 91 deleted {round_91}/1000, expected ~700"
        );
        let late_round = policy.delete_count(1000, 991);
        assert!(
            (760..=780).contains(&late_round),
            "round 991 deleted {late_round}/1000, expected ~767"
        );
        assert!(
            policy.delete_count(1000, 10_000_000) <= 900,
            "the ramp is capped at high_permille"
        );
    }

    #[test]
    fn fixed_fraction_reproduces_delete_the_worst_half() {
        let policy = ClauseDbPolicy::legacy();
        assert_eq!(policy.delete_count(1000, 1), 500);
        assert_eq!(policy.delete_count(1000, 5000), 500);
        assert_eq!(policy.delete_count(7, 1), 3, "truncates like `len / 2`");
        assert_eq!(policy.delete_count(0, 1), 0);
    }
}
