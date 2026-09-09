//! Opt-in, clock-free instrumentation for the linear-integer-arithmetic routes
//! (`QF_LIA`, and the `LIA` half of `QF_UFLIA`).
//!
//! ## Why this module exists
//!
//! `QF_LRA` got engine counters ([`crate::euf_egraph::TheoryEngineCounters`]) and
//! the first thing they did was refute the plan's stated cause
//! (`simplex_cold_restarts = 0` across 6,571 checks). The integer routes had
//! **nothing**: [`crate::lia_online::LiaTheory`] does not implement
//! `engine_counters`, so `--trace` printed no engine figure at all for a `QF_LIA`
//! or `QF_UFLIA` query, and the offline `lia-simplex` decider — which the route
//! attribution sweep found *binding* on more lost `QF_LIA` files than any other
//! route — is not a `TheorySolver` at all and could never appear there.
//!
//! ## The one rule this module is built around
//!
//! `TheoryEngineCounters`' fields are `u64`, so **`0` reads as "measured zero"**.
//! Wiring a struct in without making the integer routes actually increment it is
//! therefore worse than leaving it unwired: it manufactures confident zeros.
//! Three things defend against that here:
//!
//! 1. [`last_lia_counters`] returns [`Option`]. `None` means *collection was never
//!    enabled on this thread* — never "zero".
//! 2. Every group carries an **entry counter** that is incremented before the
//!    group can contribute anything else ([`LiaCounters::offline_calls`],
//!    [`LiaCounters::bnb_roots`], [`LiaCounters::simplex_solves`],
//!    [`LiaCounters::theory_asserts`], [`LiaCounters::propagate_calls`]). A zero
//!    *inside* a group whose entry counter is zero says "that code did not run",
//!    which is a different statement from "it ran and found nothing".
//! 3. [`LiaCounters::groups`] records the [`LiaCounterPolicy`] that was in force,
//!    so a group switched off by policy is distinguishable from a group that ran
//!    and counted zero. [`LiaCounters::group_reading`] answers all three cases in
//!    one call and is what a report should be written against.
//!
//! ## Cost when off
//!
//! One thread-local `Cell` read per recording site, no clock read, no
//! allocation — the same shape as [`crate::DlOnlineStatsGuard`],
//! `FrontDoorStatsGuard`, `BvLayerStatsGuard` and `RouteAttributionGuard`, which
//! `--trace` already composes. Nothing in this module is read by the search, so
//! no verdict can depend on whether a guard is armed.
//!
//! ## Cost when on
//!
//! The two hot sites — simplex pivots and branch-and-bound nodes — are **not**
//! recorded per event. `simplex_feasible` accumulates its pivots in a local and
//! records once at return; branch-and-bound's node count is recovered from the
//! node-budget delta at the top-level call. So arming the guard cannot change the
//! shape of the profile it is being used to read.

use std::cell::{Cell, RefCell};
use std::sync::{Arc, Mutex, PoisonError};

/// Which groups of [`LiaCounters`] a run collects.
///
/// A policy object rather than constants inlined at the recording sites, for the
/// same reason `crate::ticks`-style weights are nameable elsewhere in this tree:
/// a number is only comparable to another number gathered under the same policy,
/// and a measurement has to be able to *say* which one produced it. It is
/// carried through into the snapshot ([`LiaCounters::groups`]) so a reader never
/// has to take that on trust from a run's command line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
// One `bool` per `LiaCounterGroup`, which is what the lint's "bool soup"
// heuristic is seeing. It is not soup: the fields are not interchangeable
// options, they are the group enum written out, and
// `every_group_is_representable_in_the_policy` fails if a variant is ever added
// without one. A state machine -- the lint's suggestion -- would be wrong here,
// because the groups are independent switches, not exclusive states.
#[allow(clippy::struct_excessive_bools)]
pub struct LiaCounterPolicy {
    /// Collect the offline conjunctive decider's group: `lia_simplex_capped`
    /// entries, constraint counts, Gomory rounds/cuts, branch-and-bound nodes and
    /// the exact-rational simplex underneath both.
    pub offline: bool,
    /// Collect the online theory's group: [`crate::lia_online::LiaTheory`]
    /// asserts, feasibility checks, arena clones, warm-filter verdicts and
    /// conflict-core minimisation.
    pub theory: bool,
    /// Collect the online theory's propagation group: propagate calls, atoms
    /// scanned, LP entailment probes and literals offered.
    pub propagation: bool,
    /// Collect the warm offline decider's group (`crate::lra::warm`): how each
    /// check's constraint system was assembled, the trail delta it was updated
    /// by, and the per-literal collection cache's hit rate.
    ///
    /// Separate from [`Self::offline`] because it answers a different question.
    /// `offline` says how much the decider did; `warm` says how much of it was
    /// avoided, and a warm cache that silently degrades to a rebuild on every
    /// call has the SAME `offline_calls` as one that is working.
    pub warm: bool,
}

impl LiaCounterPolicy {
    /// Everything. The default a `--trace` run arms.
    pub const ALL: Self = Self {
        offline: true,
        theory: true,
        propagation: true,
        warm: true,
    };

    /// The offline conjunctive decider only. This is the cheapest useful policy
    /// and the right one when the question is "where does `lia-simplex` go" —
    /// the route the 2026-09-07 attribution sweep found binding on more lost
    /// `QF_LIA` files than any other.
    pub const OFFLINE_ONLY: Self = Self {
        offline: true,
        theory: false,
        propagation: false,
        warm: false,
    };

    /// The online theory only, propagation included.
    pub const THEORY_ONLY: Self = Self {
        offline: false,
        theory: true,
        propagation: true,
        warm: true,
    };

    /// Nothing. Every recording site degrades to a thread-local read and a
    /// branch.
    pub const NONE: Self = Self {
        offline: false,
        theory: false,
        propagation: false,
        warm: false,
    };
}

impl Default for LiaCounterPolicy {
    fn default() -> Self {
        Self::ALL
    }
}

/// What a group's numbers in a snapshot are allowed to be read as.
///
/// Returned by [`LiaCounters::group_reading`]. The whole point of the enum is
/// that the three cases are *not* interchangeable and a `u64` cannot tell them
/// apart on its own.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GroupReading {
    /// The policy switched this group off: its fields are structurally zero and
    /// say nothing at all about the run.
    NotCollected,
    /// The group was collected and its entry site never executed — this query
    /// did not reach that code. Its other fields are zero *because nothing ran*.
    NotReached,
    /// The group was collected and ran; its fields are measurements.
    Measured,
}

/// A counter group.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiaCounterGroup {
    /// The offline conjunctive decider (`lia-simplex`): collection, tightening,
    /// Gomory, branch-and-bound, simplex.
    Offline,
    /// The online [`crate::lia_online::LiaTheory`]'s assert/feasibility path.
    Theory,
    /// The online theory's propagation path.
    Propagation,
    /// The warm offline decider (`crate::lra::warm`): how each check's system
    /// was assembled and what the per-literal cache saved.
    Warm,
}

/// How one warm check's constraint system related to the previous check's.
///
/// Named rather than summed into a single rebuild total because a warm cache
/// that silently degrades to a rebuild on every call has the same call count and
/// the same verdicts as one that is working: it reads as a disappointing
/// performance result rather than as a bug.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WarmAssembly {
    /// The live literal list was exactly the previous one.
    Unchanged,
    /// It extended the previous one: pure append, nothing discarded.
    Extended,
    /// It was a proper prefix of the previous one — a pop.
    Shortened,
    /// The lists shared a proper prefix and then differed: a backjump that
    /// re-asserted different literals, or conflict-core minimisation dropping a
    /// literal from the middle.
    Diverged,
    /// Nothing was shared: the first check, a restart, or a wholesale change.
    ColdStart,
    /// Warming is switched off by policy, so the system was built from scratch.
    PolicyCold,
}

/// Clock-free counters for the integer-arithmetic routes. Every field is a
/// monotone total over the lifetime of the active [`LiaCountersGuard`], so a
/// per-query figure is a whole snapshot and a per-call figure is a ratio.
///
/// **Read [`LiaCounters::group_reading`] before quoting any field.** A bare `0`
/// here means one of three different things; see the module docs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct LiaCounters {
    /// The policy in force while these were gathered.
    pub groups: LiaCounterPolicyBits,

    // --- Group: offline conjunctive decider (`lia-simplex`). ----------------
    /// Entries to the offline decider `lia_simplex_capped` — every call from the
    /// front-door route, from `dpll_lia`'s inner oracle, and from every
    /// [`crate::lia_online::LiaTheory`] feasibility check and core-minimisation
    /// probe. **The offline group's entry counter.**
    pub offline_calls: u64,
    /// Linear constraints the collector produced, summed over `offline_calls`.
    /// `offline_constraints / offline_calls` is the mean system size, which is
    /// what prices one node of branch-and-bound.
    pub offline_constraints: u64,
    /// Offline calls that returned before any search: outside the fragment, an
    /// `i128` overflow while linearising, a collection timeout, or a trivially
    /// contradictory constant constraint.
    pub offline_early_exits: u64,
    /// Strict constraints the gcd-aware integer tightening turned non-strict.
    pub tightened_constraints: u64,

    /// Calls to the bounded Gomory fractional-cut engine.
    pub gomory_calls: u64,
    /// Gomory calls that returned a verdict, so branch-and-bound never ran.
    pub gomory_decided: u64,
    /// Cut-and-re-solve rounds performed, summed over `gomory_calls`.
    pub gomory_rounds: u64,
    /// Cut rows appended to the Gomory tableau, summed over `gomory_calls`.
    pub gomory_cuts: u64,
    /// Pivots performed inside the Gomory tableau's own LP, summed over
    /// `gomory_calls`.
    ///
    /// This is a **separate engine** from `simplex_pivots`: the cut engine
    /// builds its own classical integer standard form (see the soundness note
    /// above `lia_gomory_cuts` in `lra.rs`) and pivots it with its own dense
    /// Gauss–Jordan routine. Counting only `simplex_pivots` was actively
    /// misleading — on `BART-PT-020/RF-13.smt2` it reported `0` against 10,102
    /// Gomory calls, which reads as "no pivoting happened".
    pub gomory_pivots: u64,
    /// Rows of the Gomory standard-form tableau as built, summed over
    /// `gomory_calls`. With `gomory_columns` this prices one `gomory_pivots`
    /// the way `simplex_rows`/`simplex_columns` price one `simplex_pivots`.
    pub gomory_rows: u64,
    /// Columns of the Gomory standard-form tableau as built (two per original
    /// variable plus one slack per row), summed over `gomory_calls`.
    pub gomory_columns: u64,

    /// Top-level entries to branch-and-bound. **The branch-and-bound entry
    /// counter**; `bnb_nodes` is only readable against it.
    pub bnb_roots: u64,
    /// Branch-and-bound nodes explored, summed over `bnb_roots`. Recovered from
    /// the node-budget delta, so counting costs nothing per node.
    pub bnb_nodes: u64,
    /// Branch-and-bound runs that ended by exhausting the node budget rather
    /// than by deciding — the direct measurement of the node-cap incompleteness
    /// the loss census attributes files to.
    pub bnb_budget_exhausted: u64,

    /// Calls to the offline exact-rational `simplex_feasible`. **The simplex
    /// entry counter.** One per branch-and-bound node plus one per LP-relaxation
    /// probe.
    pub simplex_solves: u64,
    /// Pivots performed, summed over `simplex_solves`. Accumulated in a local
    /// and recorded once per solve.
    pub simplex_pivots: u64,
    /// Constraint rows handed to the simplex, summed over `simplex_solves`.
    /// With `simplex_columns` this prices one pivot as `O(rows × columns)`
    /// exact-rational operations.
    pub simplex_rows: u64,
    /// Columns (original variables + one slack per row), summed over
    /// `simplex_solves`.
    pub simplex_columns: u64,
    /// Solves that hit the iteration backstop or an `i128` overflow and returned
    /// no verdict.
    pub simplex_declines: u64,

    /// LP-relaxation probes (`lp_relaxation_feasibility*`) — the cheap oracle
    /// the online theory propagates from, and the only offline entry point that
    /// is not a full integer decision.
    pub lp_relaxation_calls: u64,

    // --- Group: the online theory's assert/feasibility path. ----------------
    /// [`crate::lia_online::LiaTheory`] asserts that recorded a new assignment
    /// (an idempotent re-assert is not counted). **The theory group's entry
    /// counter.**
    pub theory_asserts: u64,
    /// Feasibility decisions the theory ran — one per non-deferred assert, plus
    /// the deferred path's single check per propagate.
    pub theory_feasibility_checks: u64,
    /// `TermArena` clones the theory made to build polarity-applied live terms.
    /// One per feasibility check that got past the warm filter, and one more per
    /// propagation probe.
    pub arena_clones: u64,
    /// Arena nodes copied by those clones, summed. This is the actual cost:
    /// `arena_clone_nodes / arena_clones` is the mean arena size, and the
    /// product is the number of `TermNode`s copied for the whole query.
    pub arena_clone_nodes: u64,
    /// Live asserted literals seen by a feasibility check, summed over
    /// `theory_feasibility_checks` — the length of the conjunction rebuilt each
    /// time.
    pub live_literals: u64,
    /// Warm rational-filter verdicts that refuted the live set without touching
    /// the offline decider.
    pub filter_refuted: u64,
    /// Warm-filter verdicts that found an integral point, so the live set was
    /// accepted without the offline decider.
    pub filter_integral: u64,
    /// Warm-filter verdicts that decided nothing, so the offline decider ran.
    pub filter_inconclusive: u64,
    /// Conflict-core deletion-minimisation runs.
    pub core_minimizations: u64,
    /// Offline re-decisions performed *inside* those runs, summed — one per
    /// literal in the infeasible set. This is the counter behind "the theory
    /// re-calls the whole offline decider once per literal".
    pub core_minimization_probes: u64,

    // --- Group: the online theory's propagation path. -----------------------
    /// [`crate::lia_online::LiaTheory`] propagation calls. **The propagation
    /// group's entry counter.**
    pub propagate_calls: u64,
    /// Registered atoms the propagation scan examined, summed over
    /// `propagate_calls`. The scan visits every atom, so this is
    /// `propagate_calls × atoms` less the already-assigned ones.
    pub propagate_atoms_scanned: u64,
    /// Entailment probes actually run (each is at least one LP relaxation or one
    /// warm-engine check), summed.
    pub propagate_probes: u64,
    /// Literals the theory offered the driver, summed.
    pub propagations_offered: u64,

    // --- Group: the warm offline decider (`crate::lra::warm`). --------------
    /// Entries to the warm offline decider. **The warm group's entry counter.**
    /// Zero with `theory_feasibility_checks > 0` means the theory took the cold
    /// path, which is what `LiaWarmPolicy::OFF` does.
    pub warm_checks: u64,
    /// Checks whose constraint system continued from the previous check's
    /// rather than being built from nothing.
    pub warm_updates: u64,
    /// Checks whose constraint system was built from nothing.
    pub warm_rebuilds: u64,
    /// Checks whose live literal list was exactly the previous one.
    pub warm_assembly_unchanged: u64,
    /// Checks that appended to the previous list and discarded nothing.
    pub warm_assembly_extended: u64,
    /// Checks whose list was a proper prefix of the previous one — a pop.
    pub warm_assembly_shortened: u64,
    /// Checks sharing a proper prefix and then differing: a backjump, or
    /// conflict-core minimisation dropping a literal from the middle.
    pub warm_assembly_diverged: u64,
    /// Checks sharing nothing with the previous one.
    pub warm_assembly_cold_start: u64,
    /// Checks rebuilt because the policy switched warming off.
    pub warm_assembly_policy_cold: u64,
    /// Literals appended to the assembled system, summed over checks.
    pub warm_delta_added: u64,
    /// Literals discarded from it, summed over checks.
    pub warm_delta_removed: u64,
    /// Literals kept from the previous check, summed — the quantity warming
    /// exists to avoid recomputing.
    pub warm_delta_kept: u64,
    /// Literals collected from their term graph for the first time.
    pub warm_literal_collections: u64,
    /// Literal lookups served from the collection cache.
    pub warm_literal_cache_hits: u64,
    /// Literals not cached because the cache bound was reached.
    pub warm_literal_cache_evicted: u64,
    /// Constraints copied into the assembled system, summed over checks.
    /// Against `offline_constraints` this is the share of the system a warm
    /// update actually touched.
    pub warm_constraints_copied: u64,
    /// Feasibility checks that skipped the warm rational filter because the
    /// policy switched it off.
    ///
    /// NOT folded into `filter_inconclusive`: the filter reaching no conclusion
    /// and the filter never running are different events, and a reader dividing
    /// by the wrong one gets a wrong answer about what the filter is worth.
    pub filter_skipped: u64,
}

/// [`LiaCounterPolicy`] as it is stored inside a [`LiaCounters`] snapshot.
///
/// A separate type so [`LiaCounters`] can keep its `Default` (all zero = nothing
/// collected), which a `LiaCounterPolicy` defaulting to `ALL` would quietly
/// contradict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
// See the note on `LiaCounterPolicy`: one field per group, kept honest by
// `every_group_is_representable_in_the_policy`.
#[allow(clippy::struct_excessive_bools)]
pub struct LiaCounterPolicyBits {
    /// See [`LiaCounterPolicy::offline`].
    pub offline: bool,
    /// See [`LiaCounterPolicy::theory`].
    pub theory: bool,
    /// See [`LiaCounterPolicy::propagation`].
    pub propagation: bool,
    /// See [`LiaCounterPolicy::warm`].
    pub warm: bool,
}

impl From<LiaCounterPolicy> for LiaCounterPolicyBits {
    fn from(policy: LiaCounterPolicy) -> Self {
        Self {
            offline: policy.offline,
            theory: policy.theory,
            propagation: policy.propagation,
            warm: policy.warm,
        }
    }
}

impl LiaCounters {
    /// How this group's fields may be read: not collected, collected but never
    /// reached, or measured.
    ///
    /// This is the accessor a report must be written against. Quoting a raw
    /// field without it is the mistake the `u64` field type makes easy — a
    /// structural zero and a measured zero are the same eight bytes.
    #[must_use]
    pub fn group_reading(&self, group: LiaCounterGroup) -> GroupReading {
        let (collected, entered) = match group {
            LiaCounterGroup::Offline => (self.groups.offline, self.offline_calls > 0),
            LiaCounterGroup::Theory => (self.groups.theory, self.theory_asserts > 0),
            LiaCounterGroup::Propagation => (self.groups.propagation, self.propagate_calls > 0),
            LiaCounterGroup::Warm => (self.groups.warm, self.warm_checks > 0),
        };
        match (collected, entered) {
            (false, _) => GroupReading::NotCollected,
            (true, false) => GroupReading::NotReached,
            (true, true) => GroupReading::Measured,
        }
    }

    /// Mean linear constraints per offline decider call, or `0.0` when the
    /// decider never ran.
    #[must_use]
    pub fn constraints_per_offline_call(&self) -> f64 {
        ratio(self.offline_constraints, self.offline_calls)
    }

    /// Mean simplex solves per offline decider call — branch-and-bound nodes
    /// plus the root, so a value near `1.0` says the integer search never
    /// branched.
    #[must_use]
    pub fn simplex_solves_per_offline_call(&self) -> f64 {
        ratio(self.simplex_solves, self.offline_calls)
    }

    /// Mean arena nodes copied per online-theory assert. The size of the
    /// state-proportional work an incremental integer check would remove.
    #[must_use]
    pub fn arena_nodes_per_assert(&self) -> f64 {
        ratio(self.arena_clone_nodes, self.theory_asserts)
    }

    /// Offline decider calls attributable to conflict-core minimisation — the
    /// share of the integer decider's work that is spent explaining a refutation
    /// the theory has already found.
    #[must_use]
    pub fn core_minimization_share(&self) -> f64 {
        ratio(self.core_minimization_probes, self.offline_calls)
    }
}

fn ratio(numerator: u64, denominator: u64) -> f64 {
    if denominator == 0 {
        return 0.0;
    }
    #[allow(clippy::cast_precision_loss)]
    {
        numerator as f64 / denominator as f64
    }
}

std::thread_local! {
    /// Whether integer-route counters are being collected on this thread, and
    /// under which policy. `None` is the off state and is what makes
    /// [`last_lia_counters`] able to say "never enabled" rather than "zero".
    static LIA_POLICY: Cell<Option<LiaCounterPolicy>> = const { Cell::new(None) };
    /// The counters themselves. Only ever touched while `LIA_POLICY` is `Some`.
    static LIA_COUNTERS: Cell<LiaCounters> = const { Cell::new(none_counters()) };
    /// Whether a snapshot exists to be read: set by [`LiaCountersGuard::enable`]
    /// and never cleared, so a snapshot survives its guard's drop exactly the
    /// way `last_dl_online_stats` does.
    static LIA_ARMED: Cell<bool> = const { Cell::new(false) };
    /// The cross-thread mirror, when a [`crate::live_instruments`] board was
    /// installed at [`LiaCountersGuard::enable`] time. `None` on every ordinary
    /// run, and the decision is taken once at guard construction rather than at
    /// each recording site.
    static LIA_MIRROR: RefCell<Option<Arc<LiaCountersMirror>>> = const { RefCell::new(None) };
    /// How many recording calls have happened since the guard was constructed,
    /// for the flush cadence. Separate from [`LIA_COUNTERS`] because it counts
    /// recordings into groups the policy switched OFF too: otherwise a policy
    /// collecting only propagation would flush on a different cadence than one
    /// collecting everything, and two runs' partial readings would not be
    /// comparable.
    static LIA_RECORDS: Cell<u64> = const { Cell::new(0) };
}

/// How many recording calls pass between mirror flushes.
///
/// The same shape of choice as `cdclt`'s `LIVE_MIRROR_STEPS` and
/// `axeyum_cnf::NativeLayerStatsMirror`'s cadence: often enough that a reading
/// taken at an arbitrary kill is close to current, rare enough that the shared
/// lock is never on a hot path. At 1,024, a run doing ten million recordings
/// takes the lock under ten thousand times.
const LIVE_MIRROR_RECORDS: u64 = 1_024;

/// The cross-thread slot a **running** integer-route solve flushes its counters
/// into.
///
/// # Why a mirror rather than a publish point
///
/// Every other instrument in this tree publishes a snapshot when its stage
/// RETURNS. [`LiaCounters`] has no stage: the counters accumulate in a
/// thread-local across the whole solve and are read once at the end. A query
/// killed by a watchdog therefore published nothing at all, which made the
/// integer routes the least visible thing in exactly the runs the `QF_LIA`
/// losses are made of. This slot is written on a fixed recording cadence from
/// inside whatever loop is running, which is the only reason a solve that never
/// returns has anything to say.
///
/// The reading is always partial: every field is a monotone total, so a
/// mid-flight sample is a LOWER BOUND on each of them, and a ratio of two of
/// them is not the ratio the finished run would have reported.
#[derive(Debug, Default)]
pub struct LiaCountersMirror {
    /// The most recent flush and how many flushes have happened. `None` before
    /// the first flush, which distinguishes "this solve has not reached
    /// [`LIVE_MIRROR_RECORDS`] recordings yet" from "this solve recorded
    /// zeros".
    slot: Mutex<Option<(LiaCounters, u64)>>,
}

impl LiaCountersMirror {
    /// Stores `counters`, overwriting the previous flush and bumping the flush
    /// count. A poisoned lock is recovered rather than propagated: telemetry
    /// must never turn one panic into two.
    fn store(&self, counters: &LiaCounters) {
        let mut slot = self.slot.lock().unwrap_or_else(PoisonError::into_inner);
        let flushes = slot.map_or(0, |(_, n)| n).saturating_add(1);
        *slot = Some((*counters, flushes));
    }

    /// The most recent flush and the flush count, readable from any thread at
    /// any time. `None` until the first flush.
    #[must_use]
    pub fn sample(&self) -> Option<(LiaCounters, u64)> {
        *self.slot.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

/// The best [`LiaCounters`] reading `board` holds: the snapshot published when
/// the integer-route guard was dropped, or a partial reading flushed out of a
/// solve that is still running.
///
/// Ordered by publish sequence for the same reason
/// `crate::live_theory_layer_stats` is: a mirror installed after the last
/// completed snapshot means a solve is in flight, and its partial counters —
/// stale though they are — are the ones a reader wants. Reversing that would
/// report a finished solve's numbers for a query that is currently stuck
/// somewhere else.
///
/// **[`LiaCounters::group_reading`] still governs every field.** A partial
/// reading does not turn `NotCollected` or `NotReached` into a measurement; it
/// makes a `Measured` group a lower bound. The two distinctions are
/// independent, and a consumer has to print both.
#[must_use]
pub fn live_lia_counters(
    board: &crate::live_instruments::LiveInstruments,
) -> Option<crate::live_instruments::LiveSample<LiaCounters>> {
    use crate::live_instruments::{LiveSample, Sampled, instrument};
    let completed = board.sample::<LiaCounters>(instrument::LIA_COUNTERS);
    let in_flight = board
        .sample::<Arc<LiaCountersMirror>>(instrument::LIA_COUNTERS_MIRROR)
        .and_then(|handle| {
            let (counters, _flushes) = handle.value.sample()?;
            Some(LiveSample {
                value: counters,
                // Always partial: flushed on a recording cadence from inside
                // whatever loop is running, never at a verdict.
                sampled: Sampled::InFlight,
                sequence: handle.sequence,
            })
        });
    match (completed, in_flight) {
        (Some(done), Some(live)) if live.sequence > done.sequence => Some(live),
        (Some(done), _) => Some(done),
        (None, live) => live,
    }
}

const fn none_counters() -> LiaCounters {
    LiaCounters {
        groups: LiaCounterPolicyBits {
            offline: false,
            theory: false,
            propagation: false,
            warm: false,
        },
        offline_calls: 0,
        offline_constraints: 0,
        offline_early_exits: 0,
        tightened_constraints: 0,
        gomory_calls: 0,
        gomory_decided: 0,
        gomory_rounds: 0,
        gomory_cuts: 0,
        gomory_pivots: 0,
        gomory_rows: 0,
        gomory_columns: 0,
        bnb_roots: 0,
        bnb_nodes: 0,
        bnb_budget_exhausted: 0,
        simplex_solves: 0,
        simplex_pivots: 0,
        simplex_rows: 0,
        simplex_columns: 0,
        simplex_declines: 0,
        lp_relaxation_calls: 0,
        theory_asserts: 0,
        theory_feasibility_checks: 0,
        arena_clones: 0,
        arena_clone_nodes: 0,
        live_literals: 0,
        filter_refuted: 0,
        filter_integral: 0,
        filter_inconclusive: 0,
        core_minimizations: 0,
        core_minimization_probes: 0,
        propagate_calls: 0,
        propagate_atoms_scanned: 0,
        propagate_probes: 0,
        propagations_offered: 0,
        warm_checks: 0,
        warm_updates: 0,
        warm_rebuilds: 0,
        warm_assembly_unchanged: 0,
        warm_assembly_extended: 0,
        warm_assembly_shortened: 0,
        warm_assembly_diverged: 0,
        warm_assembly_cold_start: 0,
        warm_assembly_policy_cold: 0,
        warm_delta_added: 0,
        warm_delta_removed: 0,
        warm_delta_kept: 0,
        warm_literal_collections: 0,
        warm_literal_cache_hits: 0,
        warm_literal_cache_evicted: 0,
        warm_constraints_copied: 0,
        filter_skipped: 0,
    }
}

/// Enables integer-route counter collection on this thread for the lifetime of
/// the returned guard, restoring the previous setting on drop.
///
/// Resets the counters on `enable`, the same convention as
/// [`crate::DlOnlineStatsGuard`] / `FrontDoorStatsGuard` / `BvLayerStatsGuard` /
/// `RouteAttributionGuard`. Off by default costs one thread-local read per
/// recording site and nothing else.
pub struct LiaCountersGuard(Option<LiaCounterPolicy>);

impl LiaCountersGuard {
    /// Enables collection of every group.
    #[must_use]
    pub fn enable() -> Self {
        Self::enable_with(LiaCounterPolicy::ALL)
    }

    /// Enables collection under an explicit policy.
    #[must_use]
    pub fn enable_with(policy: LiaCounterPolicy) -> Self {
        let previous = LIA_POLICY.with(|c| c.replace(Some(policy)));
        LIA_COUNTERS.with(|c| {
            let mut counters = none_counters();
            counters.groups = policy.into();
            c.set(counters);
        });
        LIA_ARMED.with(|c| c.set(true));
        LIA_RECORDS.with(|c| c.set(0));
        // The board decision is taken HERE, once, rather than at each recording
        // site: `record` on a run with no board must keep costing exactly what
        // it cost before this existed. `installed()` is one thread-local `bool`
        // read, and on a default run (no `--trace`) it is false, so neither the
        // `Arc` nor the `Mutex` is ever constructed.
        let mirror = crate::live_instruments::installed().then(|| {
            let mirror = Arc::new(LiaCountersMirror::default());
            crate::live_instruments::publish_live(
                crate::live_instruments::instrument::LIA_COUNTERS_MIRROR,
                Arc::clone(&mirror),
                // A handle, never a snapshot: the solve writes through it for as
                // long as it runs, so a watchdog reads the latest flush without
                // the worker publishing again.
                crate::live_instruments::Sampled::InFlight,
            );
            mirror
        });
        if let Some(mirror) = mirror.as_ref() {
            // Seed the mirror with the freshly zeroed, policy-tagged snapshot.
            //
            // Without this a watchdog kill on a query that never reached the
            // integer routes prints NO `; lia` line, while the same query on the
            // completed path prints `offline=not-reached …`. Same fact, one form
            // stated and one form silent — and this instrument exists precisely
            // to keep "not reached" from reading as "zero" or as "we could not
            // see". Measured 2026-09-08: every one of the 5 `QF_LRA` files that
            // took the watchdog path was silent this way.
            //
            // Safe only because `record` also flushes at its FIRST recording:
            // the seed is overwritten the moment anything happens, so it can
            // never masquerade as a current reading of a query that has since
            // done work.
            mirror.store(&LIA_COUNTERS.with(Cell::get));
        }
        LIA_MIRROR.with(|c| *c.borrow_mut() = mirror);
        LiaCountersGuard(previous)
    }
}

impl Drop for LiaCountersGuard {
    /// Restores the previous policy and publishes the finished counters.
    ///
    /// This is the only COMPLETE publish point the instrument has, because it
    /// is the only moment at which the counters stop moving: they accumulate
    /// across the whole solve rather than being lifted at a stage boundary. It
    /// matters even for a query that later times out, because a solve can run
    /// the integer routes to completion and then be killed in a LATER stage,
    /// and `live_lia_counters` orders the two readings by publish sequence.
    fn drop(&mut self) {
        LIA_POLICY.with(|c| c.set(self.0));
        if LIA_ARMED.with(Cell::get) {
            crate::live_instruments::publish_live(
                crate::live_instruments::instrument::LIA_COUNTERS,
                LIA_COUNTERS.with(Cell::get),
                crate::live_instruments::Sampled::Complete,
            );
        }
        LIA_MIRROR.with(|c| *c.borrow_mut() = None);
    }
}

/// This thread's integer-route counters since the active (or most recently
/// dropped) [`LiaCountersGuard`] was created.
///
/// `None` means **collection was never enabled on this thread** — it is the
/// answer that keeps a caller from reading an all-zero struct as a measurement.
/// A `Some` whose fields are zero is a real statement, and
/// [`LiaCounters::group_reading`] says which of the two real statements it is.
#[must_use]
pub fn last_lia_counters() -> Option<LiaCounters> {
    LIA_ARMED
        .with(Cell::get)
        .then(|| LIA_COUNTERS.with(Cell::get))
}

/// The active policy, or `None` when collection is off on this thread.
#[inline]
fn policy() -> Option<LiaCounterPolicy> {
    LIA_POLICY.with(Cell::get)
}

/// Applies `f` to this thread's counters when `group` is being collected.
///
/// Every recording helper below funnels through here, so "collection is off"
/// costs exactly one thread-local read and one branch, and no recording site
/// can accidentally write into a group the policy switched off.
#[inline]
fn record(group: LiaCounterGroup, f: impl FnOnce(&mut LiaCounters)) {
    let Some(policy) = policy() else {
        return;
    };
    let on = match group {
        LiaCounterGroup::Offline => policy.offline,
        LiaCounterGroup::Theory => policy.theory,
        LiaCounterGroup::Propagation => policy.propagation,
        LiaCounterGroup::Warm => policy.warm,
    };
    if !on {
        return;
    }
    let counters = LIA_COUNTERS.with(|c| {
        let mut counters = c.get();
        f(&mut counters);
        c.set(counters);
        counters
    });
    // Mirror onto the cross-thread board on a fixed cadence. This is the only
    // point at which a solve that never returns says anything about the integer
    // routes: everything else here is read after the guard drops. Reached only
    // when collection is already on (the `policy()` test above returned
    // `Some`), so a default run never gets here at all, and a `--trace` run
    // pays one `Cell<u64>` read, an add and a modulo per recording.
    let records = LIA_RECORDS.with(|c| {
        let next = c.get().wrapping_add(1);
        c.set(next);
        next
    });
    // The FIRST record flushes too, not only every `LIVE_MIRROR_RECORDS`-th.
    // Without it a query killed after fewer than 1,024 recordings mirrors
    // nothing, and the watchdog path prints no `; lia` line at all — which is
    // the same output as a query that never touched the integer routes. Two
    // different facts, one token. Measured 2026-09-08 on the 27 `QF_LIA`
    // losses: 8 took the watchdog path and 7 printed no `; lia` line, and only
    // the flush at record 1 makes "the routes were never reached" separable
    // from "they were reached and the cadence had not come round".
    if records == 1 || records.is_multiple_of(LIVE_MIRROR_RECORDS) {
        mirror_lia_counters(&counters);
    }
}

/// Flushes `counters` onto the cross-thread mirror, when a board was installed
/// at [`LiaCountersGuard::enable_with`] time.
///
/// `try_borrow` rather than `borrow` for the same reason
/// `crate::live_instruments::publish_live` uses it: this is telemetry reached
/// from deep inside a search, and a re-entrant flush (which no current call
/// path produces) must drop the reading, never panic mid-solve.
fn mirror_lia_counters(counters: &LiaCounters) {
    LIA_MIRROR.with(|c| {
        if let Ok(slot) = c.try_borrow()
            && let Some(mirror) = slot.as_ref()
        {
            mirror.store(counters);
        }
    });
}

// --- Offline decider recording sites. ---------------------------------------

/// One entry to the offline conjunctive integer decider, with the number of
/// linear constraints it collected.
pub(crate) fn record_offline_call(constraints: u64) {
    record(LiaCounterGroup::Offline, |c| {
        c.offline_calls = c.offline_calls.saturating_add(1);
        c.offline_constraints = c.offline_constraints.saturating_add(constraints);
    });
}

/// An offline call that returned before any search ran.
pub(crate) fn record_offline_early_exit() {
    record(LiaCounterGroup::Offline, |c| {
        c.offline_calls = c.offline_calls.saturating_add(1);
        c.offline_early_exits = c.offline_early_exits.saturating_add(1);
    });
}

/// Strict constraints the gcd-aware tightening made non-strict in one call.
pub(crate) fn record_tightened(count: u64) {
    record(LiaCounterGroup::Offline, |c| {
        c.tightened_constraints = c.tightened_constraints.saturating_add(count);
    });
}

/// One Gomory engine run that got as far as building a tableau: whether it
/// decided, and the rounds, cuts, pivots and tableau shape it used.
///
/// `rows`/`columns` are the tableau **as built**, before cuts, which is the
/// shape `pivots` is priced against for the first round; later rounds pivot a
/// tableau `cuts` rows taller. That approximation is stated here rather than
/// hidden: an exact per-round shape would need a per-round record call in the
/// loop this deliberately keeps free of them.
pub(crate) fn record_gomory_work(
    decided: bool,
    rounds: u64,
    cuts: u64,
    pivots: u64,
    rows: u64,
    columns: u64,
) {
    record(LiaCounterGroup::Offline, |c| {
        c.gomory_calls = c.gomory_calls.saturating_add(1);
        if decided {
            c.gomory_decided = c.gomory_decided.saturating_add(1);
        }
        c.gomory_rounds = c.gomory_rounds.saturating_add(rounds);
        c.gomory_cuts = c.gomory_cuts.saturating_add(cuts);
        c.gomory_pivots = c.gomory_pivots.saturating_add(pivots);
        c.gomory_rows = c.gomory_rows.saturating_add(rows);
        c.gomory_columns = c.gomory_columns.saturating_add(columns);
    });
}

/// One top-level branch-and-bound run: the nodes it explored (recovered from the
/// node-budget delta) and whether it stopped by exhausting the budget.
pub(crate) fn record_bnb(nodes: u64, budget_exhausted: bool) {
    record(LiaCounterGroup::Offline, |c| {
        c.bnb_roots = c.bnb_roots.saturating_add(1);
        c.bnb_nodes = c.bnb_nodes.saturating_add(nodes);
        if budget_exhausted {
            c.bnb_budget_exhausted = c.bnb_budget_exhausted.saturating_add(1);
        }
    });
}

/// One exact-rational simplex solve: its pivot count, its tableau shape, and
/// whether it declined without a verdict.
pub(crate) fn record_simplex_solve(pivots: u64, rows: u64, columns: u64, declined: bool) {
    record(LiaCounterGroup::Offline, |c| {
        c.simplex_solves = c.simplex_solves.saturating_add(1);
        c.simplex_pivots = c.simplex_pivots.saturating_add(pivots);
        c.simplex_rows = c.simplex_rows.saturating_add(rows);
        c.simplex_columns = c.simplex_columns.saturating_add(columns);
        if declined {
            c.simplex_declines = c.simplex_declines.saturating_add(1);
        }
    });
}

/// One LP-relaxation probe.
pub(crate) fn record_lp_relaxation() {
    record(LiaCounterGroup::Offline, |c| {
        c.lp_relaxation_calls = c.lp_relaxation_calls.saturating_add(1);
    });
}

// --- Online theory recording sites. -----------------------------------------

/// One [`crate::lia_online::LiaTheory`] assert that recorded a new assignment.
pub(crate) fn record_theory_assert() {
    record(LiaCounterGroup::Theory, |c| {
        c.theory_asserts = c.theory_asserts.saturating_add(1);
    });
}

/// One integer-feasibility decision over `live_literals` asserted literals.
pub(crate) fn record_feasibility_check(live_literals: u64) {
    record(LiaCounterGroup::Theory, |c| {
        c.theory_feasibility_checks = c.theory_feasibility_checks.saturating_add(1);
        c.live_literals = c.live_literals.saturating_add(live_literals);
    });
}

/// One `TermArena` clone of `nodes` nodes made to build live polarity terms.
pub(crate) fn record_arena_clone(nodes: u64) {
    record(LiaCounterGroup::Theory, |c| {
        c.arena_clones = c.arena_clones.saturating_add(1);
        c.arena_clone_nodes = c.arena_clone_nodes.saturating_add(nodes);
    });
}

/// One warm rational-filter refutation.
pub(crate) fn record_filter_refuted() {
    record(LiaCounterGroup::Theory, |c| {
        c.filter_refuted = c.filter_refuted.saturating_add(1);
    });
}

/// One warm-filter integral-point acceptance; see [`record_filter_refuted`].
pub(crate) fn record_filter_integral() {
    record(LiaCounterGroup::Theory, |c| {
        c.filter_integral = c.filter_integral.saturating_add(1);
    });
}

/// One inconclusive warm-filter verdict; see [`record_filter_refuted`].
pub(crate) fn record_filter_inconclusive() {
    record(LiaCounterGroup::Theory, |c| {
        c.filter_inconclusive = c.filter_inconclusive.saturating_add(1);
    });
}

/// One feasibility check that never reached the warm filter because the policy
/// switched it off; see [`LiaCounters::filter_skipped`].
pub(crate) fn record_filter_skipped() {
    record(LiaCounterGroup::Theory, |c| {
        c.filter_skipped = c.filter_skipped.saturating_add(1);
    });
}

/// One entry to the warm offline decider. **The warm group's entry counter**,
/// incremented before anything else in the group can move.
pub(crate) fn record_warm_check() {
    record(LiaCounterGroup::Warm, |c| {
        c.warm_checks = c.warm_checks.saturating_add(1);
    });
}

/// How one check's system was assembled: which reason applied, how many literals
/// were kept, discarded and appended.
pub(crate) fn record_warm_assembly(reason: WarmAssembly, kept: u64, removed: u64, added: u64) {
    record(LiaCounterGroup::Warm, |c| {
        let slot = match reason {
            WarmAssembly::Unchanged => &mut c.warm_assembly_unchanged,
            WarmAssembly::Extended => &mut c.warm_assembly_extended,
            WarmAssembly::Shortened => &mut c.warm_assembly_shortened,
            WarmAssembly::Diverged => &mut c.warm_assembly_diverged,
            WarmAssembly::ColdStart => &mut c.warm_assembly_cold_start,
            WarmAssembly::PolicyCold => &mut c.warm_assembly_policy_cold,
        };
        *slot = slot.saturating_add(1);
        if matches!(reason, WarmAssembly::ColdStart | WarmAssembly::PolicyCold) {
            c.warm_rebuilds = c.warm_rebuilds.saturating_add(1);
        } else {
            c.warm_updates = c.warm_updates.saturating_add(1);
        }
        c.warm_delta_kept = c.warm_delta_kept.saturating_add(kept);
        c.warm_delta_removed = c.warm_delta_removed.saturating_add(removed);
        c.warm_delta_added = c.warm_delta_added.saturating_add(added);
    });
}

/// One literal collected from its term graph for the first time.
pub(crate) fn record_warm_literal_collection() {
    record(LiaCounterGroup::Warm, |c| {
        c.warm_literal_collections = c.warm_literal_collections.saturating_add(1);
    });
}

/// One literal lookup served from the collection cache.
pub(crate) fn record_warm_literal_cache_hit() {
    record(LiaCounterGroup::Warm, |c| {
        c.warm_literal_cache_hits = c.warm_literal_cache_hits.saturating_add(1);
    });
}

/// One literal not cached because the cache bound was reached.
pub(crate) fn record_warm_literal_cache_evicted() {
    record(LiaCounterGroup::Warm, |c| {
        c.warm_literal_cache_evicted = c.warm_literal_cache_evicted.saturating_add(1);
    });
}

/// Constraints copied into the assembled system by one append.
pub(crate) fn record_warm_constraints_copied(copied: u64) {
    record(LiaCounterGroup::Warm, |c| {
        c.warm_constraints_copied = c.warm_constraints_copied.saturating_add(copied);
    });
}

/// One conflict-core deletion-minimisation run and the offline re-decisions it
/// performed.
pub(crate) fn record_core_minimization(probes: u64) {
    record(LiaCounterGroup::Theory, |c| {
        c.core_minimizations = c.core_minimizations.saturating_add(1);
        c.core_minimization_probes = c.core_minimization_probes.saturating_add(probes);
    });
}

// --- Online propagation recording sites. ------------------------------------

/// One propagation call: the atoms its scan examined, the entailment probes it
/// ran, and the literals it offered.
pub(crate) fn record_propagate(atoms_scanned: u64, probes: u64, offered: u64) {
    record(LiaCounterGroup::Propagation, |c| {
        c.propagate_calls = c.propagate_calls.saturating_add(1);
        c.propagate_atoms_scanned = c.propagate_atoms_scanned.saturating_add(atoms_scanned);
        c.propagate_probes = c.propagate_probes.saturating_add(probes);
        c.propagations_offered = c.propagations_offered.saturating_add(offered);
    });
}

#[cfg(test)]
mod tests;
