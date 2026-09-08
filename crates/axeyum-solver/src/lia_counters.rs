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

use std::cell::Cell;

/// Which groups of [`LiaCounters`] a run collects.
///
/// A policy object rather than constants inlined at the recording sites, for the
/// same reason `crate::ticks`-style weights are nameable elsewhere in this tree:
/// a number is only comparable to another number gathered under the same policy,
/// and a measurement has to be able to *say* which one produced it. It is
/// carried through into the snapshot ([`LiaCounters::groups`]) so a reader never
/// has to take that on trust from a run's command line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
}

impl LiaCounterPolicy {
    /// Everything. The default a `--trace` run arms.
    pub const ALL: Self = Self {
        offline: true,
        theory: true,
        propagation: true,
    };

    /// The offline conjunctive decider only. This is the cheapest useful policy
    /// and the right one when the question is "where does `lia-simplex` go" —
    /// the route the 2026-09-07 attribution sweep found binding on more lost
    /// `QF_LIA` files than any other.
    pub const OFFLINE_ONLY: Self = Self {
        offline: true,
        theory: false,
        propagation: false,
    };

    /// The online theory only, propagation included.
    pub const THEORY_ONLY: Self = Self {
        offline: false,
        theory: true,
        propagation: true,
    };

    /// Nothing. Every recording site degrades to a thread-local read and a
    /// branch.
    pub const NONE: Self = Self {
        offline: false,
        theory: false,
        propagation: false,
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
}

/// [`LiaCounterPolicy`] as it is stored inside a [`LiaCounters`] snapshot.
///
/// A separate type so [`LiaCounters`] can keep its `Default` (all zero = nothing
/// collected), which a `LiaCounterPolicy` defaulting to `ALL` would quietly
/// contradict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct LiaCounterPolicyBits {
    /// See [`LiaCounterPolicy::offline`].
    pub offline: bool,
    /// See [`LiaCounterPolicy::theory`].
    pub theory: bool,
    /// See [`LiaCounterPolicy::propagation`].
    pub propagation: bool,
}

impl From<LiaCounterPolicy> for LiaCounterPolicyBits {
    fn from(policy: LiaCounterPolicy) -> Self {
        Self {
            offline: policy.offline,
            theory: policy.theory,
            propagation: policy.propagation,
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
}

const fn none_counters() -> LiaCounters {
    LiaCounters {
        groups: LiaCounterPolicyBits {
            offline: false,
            theory: false,
            propagation: false,
        },
        offline_calls: 0,
        offline_constraints: 0,
        offline_early_exits: 0,
        tightened_constraints: 0,
        gomory_calls: 0,
        gomory_decided: 0,
        gomory_rounds: 0,
        gomory_cuts: 0,
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
        LiaCountersGuard(previous)
    }
}

impl Drop for LiaCountersGuard {
    fn drop(&mut self) {
        LIA_POLICY.with(|c| c.set(self.0));
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
    };
    if !on {
        return;
    }
    LIA_COUNTERS.with(|c| {
        let mut counters = c.get();
        f(&mut counters);
        c.set(counters);
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

/// One Gomory engine run: whether it decided, and how many rounds and cut rows
/// it used.
pub(crate) fn record_gomory(decided: bool, rounds: u64, cuts: u64) {
    record(LiaCounterGroup::Offline, |c| {
        c.gomory_calls = c.gomory_calls.saturating_add(1);
        if decided {
            c.gomory_decided = c.gomory_decided.saturating_add(1);
        }
        c.gomory_rounds = c.gomory_rounds.saturating_add(rounds);
        c.gomory_cuts = c.gomory_cuts.saturating_add(cuts);
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
