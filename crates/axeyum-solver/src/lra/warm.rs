//! A **warm** front end for the offline conjunctive `QF_LIA` decider.
//!
//! # The shape this fixes
//!
//! [`super::lia_simplex_capped`] is a pure function of an assertion list: every
//! entry builds a fresh `IntCollector`, walks every assertion's term graph,
//! linearizes it into exact rationals, integer-tightens the whole constraint set,
//! and only then hands the system to the Gomory cut round and branch-and-bound.
//!
//! Its dominant caller does not have a fresh problem each time. The lazy-SMT
//! loops ([`crate::lia_online::LiaTheory`], and through it the `QF_UFLIA`
//! combination) drive it from a `DPLL` **trail**: each call's literal list differs
//! from the previous one by an appended suffix, a popped suffix, or both. On the
//! `QF_LIA`/`QF_UFLIA` files this solver loses, that adds up to hundreds of
//! thousands of entries per file, every one of which redoes the collection and
//! the tightening for a system it had already built.
//!
//! This module keeps that work. It is *not* a memo table on verdicts (a verdict
//! cache would be a soundness liability with nothing to gain — the systems
//! genuinely differ from call to call); it caches the two stages whose result is
//! a **function of one literal alone**:
//!
//! * collection — the term walk and linearization of one polarity-applied atom;
//! * tightening — the gcd-aware strict-to-non-strict rewrite, which
//!   [`super::tighten_int_constraints`] applies constraint by constraint.
//!
//! and it keeps the assembled system across calls, updating it by the trail
//! delta rather than rebuilding it.
//!
//! # Why the answers are the SAME answers, not merely sound ones
//!
//! It would be easy to build a warm decider that is sound but decides a
//! different set of cases: both engines below are sound on any input, so a warm
//! path that permuted columns or carried spare ones could never return a wrong
//! `sat`/`unsat` — it would just answer `unknown` somewhere the cold path
//! answers, or the reverse, and no test would say so. That is a coverage change
//! disguised as a performance change.
//!
//! So this decider reproduces the cold path's system **exactly**, column
//! numbering included:
//!
//! * The persistent collector assigns each symbol a stable *global* column. That
//!   numbering is NOT what the cold path would produce for a given live list, so
//!   it is never handed to the engines.
//! * Each literal records the global columns it touches, in touch order (see
//!   `IntCollector::record_touches`) — repeats included, because a column first
//!   seen inside some other literal must still take its place in this literal's
//!   order when that other literal is not live.
//! * Assembly walks the live literals in order and allocates a *local* column on
//!   first touch. The cold numbering is precisely
//!   `dedup(concat(touch_log(l) for l in live order))`, so the local numbering
//!   and the cold numbering agree constraint for constraint.
//!
//! `nvars`, the constraint order, the `origin` tags, the tightening and the
//! engine dispatch are then identical, so the warm and cold paths are the same
//! computation — which is what makes the differential tests below a real check
//! rather than a check of two sound engines against each other.
//!
//! # What is delta-proportional and what is not
//!
//! A `DPLL` trail changes by a suffix, so the live literal lists across calls
//! share a prefix; and because a local column is allocated at the *first* live
//! literal that touches it, a shared prefix of literals has a shared prefix of
//! local columns and a shared prefix of constraints. Assembly therefore truncates
//! to the longest common prefix and appends the rest: the work is proportional to
//! the delta, not to the live set.
//!
//! Two callers break the prefix property and are counted, not hidden:
//! conflict-core minimization drops a literal from the *middle* of the list, and
//! a restart replaces the list wholesale. Both fall back to rebuilding from the
//! common prefix — still not a cold start, since the per-literal collection cache
//! survives — and [`LiaWarmCounters::assembly_reasons`] says how often.
//!
//! What is NOT warmed here is the standard-form tableau or the LP itself.
//! `build_gomory_tableau` writes a dense `m` by `2*nvars` body whose column
//! layout is a function of `nvars`, so it changes shape whenever the live
//! variable footprint does; and the tableau the cut round leaves behind has been
//! pivoted away from that layout. Warm-starting it is separate work with a
//! separate soundness argument, and this module's counters are what say whether
//! it is worth doing.

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

// Native uses the std clock; wasm uses the `web_time` drop-in (ADR-0017).
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use axeyum_ir::{SymbolId, TermArena, TermId, Value, eval};

use super::{
    Constraint, IntCollector, LiaBnb, LinExpr, decide_int_constraints, lia_bnb_undecided,
    lia_collection_timeout, past_deadline, tighten_int_constraints,
};
use crate::backend::{CheckResult, SolverError, UnknownKind, UnknownReason};
use crate::model::Model;

// ---------------------------------------------------------------------------
// Policy
// ---------------------------------------------------------------------------

/// Whether — and how — a caller warms the offline conjunctive `QF_LIA` decider.
///
/// A policy object rather than a compiled-in behaviour, because the only honest
/// way to report what warming bought is to run both arms from **one binary**:
/// two builds differ in more than the change under test, and this repository has
/// already been burned by a prebuilt binary describing an older tree. With
/// [`LiaWarmPolicy::OFF`] every field below is inert and the caller takes the
/// pre-existing cold path verbatim, so an A/B is a policy flip.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LiaWarmPolicy {
    /// Reuse the collected, tightened constraint system across checks.
    ///
    /// `false` restores the cold path exactly: a fresh collector walk, a fresh
    /// tightening pass and a fresh assembly on every call.
    pub warm: bool,
    /// Reuse each literal's polarity-applied term instead of cloning the whole
    /// arena per check.
    ///
    /// The cold path clones the theory's arena on every feasibility check purely
    /// so that building `(not atom)` cannot mutate it. Building those negations
    /// **once**, at construction, removes the clone; term interning makes the
    /// resulting ids stable, so nothing downstream can tell the difference. This
    /// is separate from [`Self::warm`] because it is a separate cost with a
    /// separate measurement, and one flag would conflate them.
    pub reuse_polarity_terms: bool,
    /// Run the warm rational filter in front of the offline decider.
    ///
    /// **Left ON by default, against the hypothesis this module started from.**
    /// The brief was that the filter refutes nothing on the loss population and
    /// should be deleted. Measured on the 29 `QF_LIA`/`QF_UFLIA` losses where the
    /// online theory is actually entered (2026-09-08, 8 s budget, the A/B in
    /// `docs/research/12-performance/lia-warm-decider-2026-09-08.md`), it
    /// answered 79,763 live sets and **refuted 20,102** of them. Switching it off
    /// pushes all of that onto the offline decider and costs 24% of the live-set
    /// decisions the lazy loop gets through in the same budget — a loss, not a
    /// saving.
    ///
    /// `false` skips it. That arm exists to isolate warming's contribution from
    /// the filter's, which is the only way either number means anything; it is
    /// not a recommended configuration.
    pub rational_filter: bool,
    /// Upper bound on the number of distinct literals whose collection is cached.
    ///
    /// A cached literal costs its own constraints, and the population is the atom
    /// set of one query, so this is a runaway-memory backstop rather than a
    /// tuning knob. Past it, literals are collected per check as the cold path
    /// does, and [`LiaWarmCounters::literal_cache_evicted`] records that it fired.
    pub max_cached_literals: usize,
}

/// Backstop on cached literals; see [`LiaWarmPolicy::max_cached_literals`].
///
/// Two literals per registered atom, and the online `LIA` theory is only built
/// for atom sets below its own admission bound, so this is not expected to fire
/// on any query that theory accepts — it exists so a caller which does not share
/// that bound cannot make this cache unbounded.
pub const DEFAULT_MAX_CACHED_LIA_LITERALS: usize = 1 << 16;

impl LiaWarmPolicy {
    /// Warming on, per-check arena cloning off, rational filter kept: the
    /// measured-best configuration and the default.
    pub const WARM: Self = Self {
        warm: true,
        reuse_polarity_terms: true,
        rational_filter: true,
        max_cached_literals: DEFAULT_MAX_CACHED_LIA_LITERALS,
    };

    /// Everything off — the pre-existing cold path, verbatim. The A/B baseline.
    pub const OFF: Self = Self {
        warm: false,
        reuse_polarity_terms: false,
        rational_filter: true,
        max_cached_literals: 0,
    };

    /// Warming on with the rational filter switched off, for isolating the
    /// filter's contribution from warming's.
    ///
    /// A diagnostic arm, not a recommended configuration: on the loss population
    /// it decides 24% FEWER live sets in the same budget than [`Self::WARM`],
    /// because every live set the filter would have answered cheaply goes to the
    /// offline decider instead.
    pub const WARM_NO_FILTER: Self = Self {
        rational_filter: false,
        ..Self::WARM
    };

    /// Whether this policy leaves every pre-existing behaviour in place.
    #[must_use]
    pub const fn is_cold(self) -> bool {
        !self.warm && !self.reuse_polarity_terms && self.rational_filter
    }
}

impl Default for LiaWarmPolicy {
    fn default() -> Self {
        Self::WARM
    }
}

/// The policy in force for callers that do not choose one explicitly.
///
/// Read once per process from `AXEYUM_LIA_WARM`:
///
/// * `off` or `0` — [`LiaWarmPolicy::OFF`], the pre-warm cold path;
/// * `nofilter` — [`LiaWarmPolicy::WARM_NO_FILTER`];
/// * anything else, or unset — [`LiaWarmPolicy::WARM`].
///
/// An override rather than a rebuild, so that both arms of a measurement come
/// from one binary (see [`LiaWarmPolicy`]).
#[must_use]
pub fn ambient_lia_warm_policy() -> LiaWarmPolicy {
    static POLICY: std::sync::OnceLock<LiaWarmPolicy> = std::sync::OnceLock::new();
    *POLICY.get_or_init(|| match std::env::var("AXEYUM_LIA_WARM") {
        Ok(value) if value.eq_ignore_ascii_case("off") || value == "0" => LiaWarmPolicy::OFF,
        Ok(value) if value.eq_ignore_ascii_case("nofilter") => LiaWarmPolicy::WARM_NO_FILTER,
        _ => LiaWarmPolicy::WARM,
    })
}

// ---------------------------------------------------------------------------
// Counters
// ---------------------------------------------------------------------------

/// Why one check could not simply continue from the previous check's assembled
/// system.
///
/// These are named rather than summed into one `rebuilds` total because a warm
/// cache that silently degrades to a rebuild on every call has the same call
/// count and the same verdicts as one that is working: it reads as a
/// disappointing performance result rather than as a bug.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssemblyReason {
    /// The live list is exactly the previous one — no assembly work at all.
    Unchanged,
    /// The live list extends the previous one: pure append, nothing discarded.
    Extended,
    /// The live list is a proper prefix of the previous one: a pop, with nothing
    /// collected.
    Shortened,
    /// The lists share a proper prefix and then differ — a backjump that
    /// re-asserted different literals, or conflict-core minimization dropping a
    /// literal from the middle of the set.
    Diverged,
    /// Nothing was shared: the first check, a restart, or a wholesale change.
    ColdStart,
    /// [`LiaWarmPolicy::warm`] is off, so the system was built from scratch.
    PolicyCold,
}

impl AssemblyReason {
    /// A stable, lowercase name for a report.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Unchanged => "unchanged",
            Self::Extended => "extended",
            Self::Shortened => "shortened",
            Self::Diverged => "diverged",
            Self::ColdStart => "cold-start",
            Self::PolicyCold => "policy-cold",
        }
    }

    /// Every variant, in report order.
    #[must_use]
    pub const fn all() -> [Self; 6] {
        [
            Self::Unchanged,
            Self::Extended,
            Self::Shortened,
            Self::Diverged,
            Self::ColdStart,
            Self::PolicyCold,
        ]
    }

    /// This reason's index into [`LiaWarmCounters::assembly_reasons`].
    #[must_use]
    pub const fn slot(self) -> usize {
        match self {
            Self::Unchanged => 0,
            Self::Extended => 1,
            Self::Shortened => 2,
            Self::Diverged => 3,
            Self::ColdStart => 4,
            Self::PolicyCold => 5,
        }
    }
}

/// Clock-free counters for the warm decider.
///
/// Every field is a `u64`, so a `0` is indistinguishable from "never collected"
/// — which is why [`last_lia_warm_stats`] returns an [`Option`] and why
/// [`LiaWarmCounters::checks`] is incremented before anything else can move. A
/// zero anywhere below with `checks > 0` is a measurement; with `checks == 0` it
/// says the decider was never entered on this thread.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct LiaWarmCounters {
    /// Entries into [`WarmLiaDecider::check`] — the group's entry counter.
    pub checks: u64,
    /// Checks whose assembled system continued from the previous one rather than
    /// being built from nothing.
    pub warm_updates: u64,
    /// Checks whose assembled system was built from nothing.
    pub rebuilds: u64,
    /// Per-[`AssemblyReason`] check counts, indexed by [`AssemblyReason::slot`].
    pub assembly_reasons: [u64; 6],
    /// Literals appended to the assembled system, summed over checks.
    pub delta_added: u64,
    /// Literals discarded from the assembled system, summed over checks.
    pub delta_removed: u64,
    /// Literals kept from the previous check, summed over checks — the quantity
    /// warming exists to avoid recomputing.
    pub delta_kept: u64,
    /// Literals collected from their term graph for the first time.
    pub literal_collections: u64,
    /// Literal lookups served from the collection cache.
    pub literal_cache_hits: u64,
    /// Literals not cached because [`LiaWarmPolicy::max_cached_literals`] was
    /// reached.
    pub literal_cache_evicted: u64,
    /// Constraints copied into the assembled system, summed over checks. Compare
    /// against `assembled_constraints_live` to see how much of the system a warm
    /// update actually touched.
    pub assembled_constraints_copied: u64,
    /// Constraints in the assembled system at the point it was handed to the
    /// engines, summed over checks.
    pub assembled_constraints_live: u64,
    /// Local columns in the assembled system when handed to the engines, summed
    /// over checks.
    pub assembled_columns_live: u64,
    /// Checks that ended in `unsat`.
    pub verdict_unsat: u64,
    /// Checks that ended in `sat`, model replayed.
    pub verdict_sat: u64,
    /// Checks that ended in `unknown`.
    pub verdict_unknown: u64,
    /// Checks that ended in a [`SolverError`] — input outside the conjunctive
    /// linear-integer fragment, or a replay failure.
    pub verdict_error: u64,
    /// Offline conjunctive decisions the online `LIA` theory asked for, counted
    /// on **both** arms — warm and cold.
    ///
    /// This is the field an A/B is scored on, and it is separate from
    /// [`Self::checks`] for a reason: `checks` only moves on the warm arm, so
    /// comparing it across arms would compare a number against zero. The loss
    /// population is budget-bound — nearly every file spends its whole timeout in
    /// either arm — so wall time cannot be the measure; how many decisions the
    /// lazy loop got through in the same budget can.
    pub theory_offline_checks: u64,
    /// Of [`Self::theory_offline_checks`], those that took the cold path (a fresh
    /// collector walk and a fresh tightening pass).
    pub theory_cold_checks: u64,
    /// Offline decisions the online theory did NOT have to make because the warm
    /// rational filter answered first. Counted on both arms, so the filter's
    /// contribution is visible where it is switched off as well as where it is on.
    pub theory_filter_answers: u64,
    /// Of [`Self::theory_filter_answers`], those that were **refutations**. The
    /// number the case for gating the filter rests on.
    pub theory_filter_refuted: u64,
}

/// Records one offline conjunctive decision the online `LIA` theory asked for.
/// See [`LiaWarmCounters::theory_offline_checks`].
pub fn record_theory_offline_check(cold: bool) {
    bump(Slot::TheoryOfflineChecks, 1);
    if cold {
        bump(Slot::TheoryColdChecks, 1);
    }
}

/// Records one live set the warm rational filter answered outright.
/// See [`LiaWarmCounters::theory_filter_answers`].
pub fn record_theory_filter_answer(refuted: bool) {
    bump(Slot::TheoryFilterAnswers, 1);
    if refuted {
        bump(Slot::TheoryFilterRefuted, 1);
    }
}

impl LiaWarmCounters {
    /// The check count for one assembly reason.
    #[must_use]
    pub const fn assembly_reason(&self, reason: AssemblyReason) -> u64 {
        self.assembly_reasons[reason.slot()]
    }

    /// A one-line, stable rendering for a trace or a sweep log.
    #[must_use]
    pub fn summary(&self) -> String {
        let mut out = format!(
            "warm=measured checks={} warm_updates={} rebuilds={} delta_added={} \
             delta_removed={} delta_kept={} literal_collections={} literal_cache_hits={} \
             literal_cache_evicted={} constraints_copied={} constraints_live={} \
             columns_live={} unsat={} sat={} unknown={} error={} theory_offline_checks={} \
             theory_cold_checks={} theory_filter_answers={} theory_filter_refuted={}",
            self.checks,
            self.warm_updates,
            self.rebuilds,
            self.delta_added,
            self.delta_removed,
            self.delta_kept,
            self.literal_collections,
            self.literal_cache_hits,
            self.literal_cache_evicted,
            self.assembled_constraints_copied,
            self.assembled_constraints_live,
            self.assembled_columns_live,
            self.verdict_unsat,
            self.verdict_sat,
            self.verdict_unknown,
            self.verdict_error,
            self.theory_offline_checks,
            self.theory_cold_checks,
            self.theory_filter_answers,
            self.theory_filter_refuted,
        );
        for reason in AssemblyReason::all() {
            let _ = write!(
                out,
                " assembly_{}={}",
                reason.name(),
                self.assembly_reason(reason)
            );
        }
        out
    }
}

/// The counter slots, in the order they are stored.
///
/// An index enum rather than a struct of atomics, so that adding a counter is
/// one line in three places the compiler checks (`Slot`, `SLOT_COUNT`,
/// [`snapshot`]) instead of a field that silently reads zero because nobody
/// wired it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(usize)]
enum Slot {
    Checks = 0,
    WarmUpdates,
    Rebuilds,
    // The six assembly reasons occupy `ASSEMBLY_BASE .. ASSEMBLY_BASE + 6`.
    AssemblyUnchanged,
    AssemblyExtended,
    AssemblyShortened,
    AssemblyDiverged,
    AssemblyColdStart,
    AssemblyPolicyCold,
    DeltaAdded,
    DeltaRemoved,
    DeltaKept,
    LiteralCollections,
    LiteralCacheHits,
    LiteralCacheEvicted,
    ConstraintsCopied,
    ConstraintsLive,
    ColumnsLive,
    VerdictUnsat,
    VerdictSat,
    VerdictUnknown,
    VerdictError,
    TheoryOfflineChecks,
    TheoryColdChecks,
    TheoryFilterAnswers,
    TheoryFilterRefuted,
}

/// The slot the first [`AssemblyReason`] occupies; the rest follow in
/// [`AssemblyReason::slot`] order.
const ASSEMBLY_BASE: usize = Slot::AssemblyUnchanged as usize;

/// How many slots there are.
const SLOT_COUNT: usize = Slot::TheoryFilterRefuted as usize + 1;

/// The six assembly-reason slots, in [`AssemblyReason::slot`] order.
const ASSEMBLY_SLOTS: [Slot; 6] = [
    Slot::AssemblyUnchanged,
    Slot::AssemblyExtended,
    Slot::AssemblyShortened,
    Slot::AssemblyDiverged,
    Slot::AssemblyColdStart,
    Slot::AssemblyPolicyCold,
];

/// The counters, shared across threads.
///
/// **Process-global and atomic, not thread-local, deliberately.** The workload
/// this instrument exists to measure is budget-bound: the solve runs on a worker
/// thread and a watchdog on the main thread gives up on it, so a thread-local
/// snapshot is unreachable on exactly the files that matter — measured here,
/// every one of the six hardest `QF_UFLIA` losses printed no counters at all
/// under a thread-local design, which is an instrument that goes blind precisely
/// where the question is. Relaxed monotone adds are the whole synchronisation:
/// no counter is read by the search, so no verdict can depend on the ordering,
/// and a reader on another thread sees a consistent-enough live total for a
/// diagnostic.
static SLOTS: [AtomicU64; SLOT_COUNT] = [const { AtomicU64::new(0) }; SLOT_COUNT];

/// Whether a [`LiaWarmProcessStatsGuard`] is armed.
static PROCESS_COLLECT: AtomicBool = AtomicBool::new(false);

/// Set once a process-wide guard has ever been armed, so a reader can tell
/// "measured zero" from "never collected".
static PROCESS_EVER_ARMED: AtomicBool = AtomicBool::new(false);

thread_local! {
    /// Whether a [`LiaWarmStatsGuard`] is armed on this thread.
    static THREAD_COLLECT: Cell<bool> = const { Cell::new(false) };
    /// Set once a thread-local guard has ever been armed on this thread.
    static THREAD_EVER_ARMED: Cell<bool> = const { Cell::new(false) };
    /// This thread's own slots.
    static THREAD_SLOTS: RefCell<[u64; SLOT_COUNT]> =
        const { RefCell::new([0; SLOT_COUNT]) };
}

/// Adds `n` to one counter, into whichever collectors are armed.
///
/// With neither armed this is one relaxed atomic load, one thread-local read and
/// a branch: no clock, no allocation, and nothing the search can observe — so no
/// verdict can depend on whether a guard exists.
fn bump(slot: Slot, n: u64) {
    if n == 0 {
        return;
    }
    if PROCESS_COLLECT.load(Ordering::Relaxed) {
        SLOTS[slot as usize].fetch_add(n, Ordering::Relaxed);
    }
    if THREAD_COLLECT.with(Cell::get) {
        THREAD_SLOTS.with(|slots| slots.borrow_mut()[slot as usize] += n);
    }
}

/// Builds a snapshot from whichever backing store `read` indexes.
fn assemble_counters(read: impl Fn(usize) -> u64) -> LiaWarmCounters {
    let mut assembly_reasons = [0u64; 6];
    for (index, entry) in assembly_reasons.iter_mut().enumerate() {
        *entry = read(ASSEMBLY_BASE + index);
    }
    LiaWarmCounters {
        checks: read(Slot::Checks as usize),
        warm_updates: read(Slot::WarmUpdates as usize),
        rebuilds: read(Slot::Rebuilds as usize),
        assembly_reasons,
        delta_added: read(Slot::DeltaAdded as usize),
        delta_removed: read(Slot::DeltaRemoved as usize),
        delta_kept: read(Slot::DeltaKept as usize),
        literal_collections: read(Slot::LiteralCollections as usize),
        literal_cache_hits: read(Slot::LiteralCacheHits as usize),
        literal_cache_evicted: read(Slot::LiteralCacheEvicted as usize),
        assembled_constraints_copied: read(Slot::ConstraintsCopied as usize),
        assembled_constraints_live: read(Slot::ConstraintsLive as usize),
        assembled_columns_live: read(Slot::ColumnsLive as usize),
        verdict_unsat: read(Slot::VerdictUnsat as usize),
        verdict_sat: read(Slot::VerdictSat as usize),
        verdict_unknown: read(Slot::VerdictUnknown as usize),
        verdict_error: read(Slot::VerdictError as usize),
        theory_offline_checks: read(Slot::TheoryOfflineChecks as usize),
        theory_cold_checks: read(Slot::TheoryColdChecks as usize),
        theory_filter_answers: read(Slot::TheoryFilterAnswers as usize),
        theory_filter_refuted: read(Slot::TheoryFilterRefuted as usize),
    }
}

/// Enables warm-decider counter collection **on this thread**, for the guard's
/// lifetime, and zeroes this thread's counters.
///
/// This is the guard a unit test wants: thread-local, so a test's numbers cannot
/// be polluted by whatever else the harness is running in parallel. For a solve
/// that runs on a worker thread and is read from another — the case that matters
/// on a budget-bound file — use [`LiaWarmProcessStatsGuard`].
#[derive(Debug)]
pub struct LiaWarmStatsGuard(bool);

impl LiaWarmStatsGuard {
    /// Arms this thread's collection and zeroes this thread's counters.
    #[must_use]
    pub fn enable() -> Self {
        let previous = THREAD_COLLECT.with(|c| c.replace(true));
        THREAD_EVER_ARMED.with(|c| c.set(true));
        THREAD_SLOTS.with(|slots| *slots.borrow_mut() = [0; SLOT_COUNT]);
        LiaWarmStatsGuard(previous)
    }
}

impl Drop for LiaWarmStatsGuard {
    fn drop(&mut self) {
        THREAD_COLLECT.with(|c| c.set(self.0));
    }
}

/// This thread's warm-decider counters since the active — or most recently
/// dropped — [`LiaWarmStatsGuard`] was created.
///
/// `None` means a thread-local guard was **never armed on this thread**, which
/// is not the same statement as every counter being zero. That distinction is
/// the whole reason for the [`Option`].
#[must_use]
pub fn last_lia_warm_stats() -> Option<LiaWarmCounters> {
    if !THREAD_EVER_ARMED.with(Cell::get) {
        return None;
    }
    Some(THREAD_SLOTS.with(|slots| {
        let slots = *slots.borrow();
        assemble_counters(|index| slots[index])
    }))
}

/// Enables warm-decider counter collection **process-wide**, for the guard's
/// lifetime, and zeroes the shared counters.
///
/// Why this exists at all, given the thread-local guard above: the workload this
/// instrument is for is budget-bound. The solve runs on a worker thread and a
/// watchdog on the main thread gives up on it, so a thread-local snapshot is
/// unreachable on exactly the files that matter — measured 2026-09-08, every one
/// of the six hardest `QF_UFLIA` losses printed no counters at all, which is an
/// instrument that goes blind precisely where the question is.
///
/// Counts from every thread land in one set of totals. Relaxed monotone adds are
/// the whole synchronisation: nothing here is read by the search, so no verdict
/// can depend on the ordering.
#[derive(Debug)]
pub struct LiaWarmProcessStatsGuard(bool);

impl LiaWarmProcessStatsGuard {
    /// Arms process-wide collection and zeroes the shared counters.
    #[must_use]
    pub fn enable() -> Self {
        let previous = PROCESS_COLLECT.swap(true, Ordering::Relaxed);
        PROCESS_EVER_ARMED.store(true, Ordering::Relaxed);
        for slot in &SLOTS {
            slot.store(0, Ordering::Relaxed);
        }
        LiaWarmProcessStatsGuard(previous)
    }
}

impl Drop for LiaWarmProcessStatsGuard {
    fn drop(&mut self) {
        PROCESS_COLLECT.store(self.0, Ordering::Relaxed);
    }
}

/// The process-wide warm-decider counters since the active — or most recently
/// dropped — [`LiaWarmProcessStatsGuard`] was created.
///
/// `None` means a process-wide guard was never armed. Safe to call while a solve
/// is still running on another thread: the counters are monotone, so a live read
/// is a lower bound on the work done so far, not a torn value. That is the whole
/// point — the files this measures never let the solve return.
#[must_use]
pub fn live_lia_warm_stats() -> Option<LiaWarmCounters> {
    if !PROCESS_EVER_ARMED.load(Ordering::Relaxed) {
        return None;
    }
    Some(assemble_counters(|index| {
        SLOTS[index].load(Ordering::Relaxed)
    }))
}

// ---------------------------------------------------------------------------
// The per-literal collection cache
// ---------------------------------------------------------------------------

/// One literal's collected, tightened contribution, in the persistent
/// collector's **global** column space.
#[derive(Debug, Clone)]
struct LiteralEntry {
    /// Tightened constraints; `origin` is stamped by assembly, not here.
    constraints: Vec<Constraint>,
    /// Global columns in touch order, duplicates removed but order preserved.
    touched: Vec<usize>,
    /// This literal is `false` on its own (a `BoolConst` at the wrong polarity).
    trivially_unsat: bool,
    /// Linearizing this literal overflowed `i128`.
    overflow: bool,
    /// This literal mentions an opaque integer `UF` application.
    has_opaque: bool,
}

// ---------------------------------------------------------------------------
// The assembled system
// ---------------------------------------------------------------------------

/// `global_to_local` entry for a global column with no live local column.
const NO_LOCAL: usize = usize::MAX;

/// The live system in **local** column space, plus the bookkeeping that lets a
/// later check truncate it to a shared prefix and append the rest.
#[derive(Debug, Default)]
struct Assembly {
    /// Literal keys in live order.
    keys: Vec<usize>,
    /// `constraints.len()` after literal `i` was appended.
    key_constraint_end: Vec<usize>,
    /// `local_to_global.len()` after literal `i` was appended.
    key_column_end: Vec<usize>,
    /// Prefix-or of `trivially_unsat` through literal `i`.
    key_trivially_unsat: Vec<bool>,
    /// Prefix-or of `overflow` through literal `i`.
    key_overflow: Vec<bool>,
    /// Prefix-or of `has_opaque` through literal `i`.
    key_opaque: Vec<bool>,
    /// The assembled constraints, in local column space.
    constraints: Vec<Constraint>,
    /// Local column `l` is global column `local_to_global[l]`.
    local_to_global: Vec<usize>,
    /// Inverse of `local_to_global`, sized to the global column count and
    /// [`NO_LOCAL`] wherever the global column is not live.
    global_to_local: Vec<usize>,
}

impl Assembly {
    /// Drops every literal from position `keep` on, restoring the local column
    /// numbering to what it was after literal `keep - 1`.
    fn truncate(&mut self, keep: usize) {
        if keep >= self.keys.len() {
            return;
        }
        let columns = if keep == 0 {
            0
        } else {
            self.key_column_end[keep - 1]
        };
        let constraints = if keep == 0 {
            0
        } else {
            self.key_constraint_end[keep - 1]
        };
        for &global in &self.local_to_global[columns..] {
            self.global_to_local[global] = NO_LOCAL;
        }
        self.local_to_global.truncate(columns);
        self.constraints.truncate(constraints);
        self.keys.truncate(keep);
        self.key_constraint_end.truncate(keep);
        self.key_column_end.truncate(keep);
        self.key_trivially_unsat.truncate(keep);
        self.key_overflow.truncate(keep);
        self.key_opaque.truncate(keep);
    }

    fn clear(&mut self) {
        self.truncate(0);
    }

    /// The local column for `global`, allocating one on its first live touch.
    /// Allocation order is touch order, which is what makes the local numbering
    /// equal the cold path's.
    fn local_of(&mut self, global: usize) -> usize {
        if global >= self.global_to_local.len() {
            self.global_to_local.resize(global + 1, NO_LOCAL);
        }
        let existing = self.global_to_local[global];
        if existing != NO_LOCAL {
            return existing;
        }
        let local = self.local_to_global.len();
        self.local_to_global.push(global);
        self.global_to_local[global] = local;
        local
    }

    /// Appends one cached literal at live position `origin`, returning how many
    /// constraints were copied.
    fn append(&mut self, key: usize, entry: &LiteralEntry, origin: usize) -> usize {
        for &global in &entry.touched {
            let _ = self.local_of(global);
        }
        let before = self.constraints.len();
        for constraint in &entry.constraints {
            let mut coeffs = BTreeMap::new();
            for (&global, &coeff) in &constraint.expr.coeffs {
                let local = self.global_to_local[global];
                debug_assert_ne!(
                    local, NO_LOCAL,
                    "a cached constraint mentions a column its own literal did not touch"
                );
                coeffs.insert(local, coeff);
            }
            self.constraints.push(Constraint {
                expr: LinExpr {
                    coeffs,
                    constant: constraint.expr.constant,
                },
                strict: constraint.strict,
                mult: Vec::new(),
                origin,
            });
        }
        let previous = self.keys.len();
        let trivially_unsat =
            entry.trivially_unsat || (previous > 0 && self.key_trivially_unsat[previous - 1]);
        let overflow = entry.overflow || (previous > 0 && self.key_overflow[previous - 1]);
        let opaque = entry.has_opaque || (previous > 0 && self.key_opaque[previous - 1]);
        self.keys.push(key);
        self.key_constraint_end.push(self.constraints.len());
        self.key_column_end.push(self.local_to_global.len());
        self.key_trivially_unsat.push(trivially_unsat);
        self.key_overflow.push(overflow);
        self.key_opaque.push(opaque);
        self.constraints.len() - before
    }

    fn trivially_unsat(&self) -> bool {
        self.key_trivially_unsat.last().copied().unwrap_or(false)
    }

    fn overflow(&self) -> bool {
        self.key_overflow.last().copied().unwrap_or(false)
    }

    fn has_opaque(&self) -> bool {
        self.key_opaque.last().copied().unwrap_or(false)
    }
}

// ---------------------------------------------------------------------------
// The decider
// ---------------------------------------------------------------------------

/// A warm front end for the offline conjunctive `QF_LIA` decider, over a **fixed
/// literal table**.
///
/// The caller assigns every literal it can ever assert a dense key and supplies
/// the polarity-applied term for each; [`WarmLiaDecider::check`] then takes the
/// live keys in trail order. Keys are the cache's identity, so the table must not
/// change for the life of the decider — which matches every caller here, whose
/// atom set is fixed when its theory is built.
#[derive(Debug)]
pub struct WarmLiaDecider {
    policy: LiaWarmPolicy,
    /// Polarity-applied term per literal key, in the caller's arena. `None` for a
    /// key the caller never asserts a constraint for.
    lit_terms: Vec<Option<TermId>>,
    /// Persistent collector: the global column space and its symbol table.
    collector: IntCollector,
    /// Global column to symbol, for model lifting. `None` for opaque columns.
    global_symbols: Vec<Option<SymbolId>>,
    /// Global columns that came from an opaque `UF` application.
    global_opaque: Vec<bool>,
    /// Per-key collection cache.
    cache: Vec<Option<LiteralEntry>>,
    cached_literals: usize,
    assembly: Assembly,
}

impl WarmLiaDecider {
    /// Builds a decider over `lit_terms`, whose index is the literal key.
    #[must_use]
    pub fn new(
        policy: LiaWarmPolicy,
        allow_opaque_apps: bool,
        lit_terms: Vec<Option<TermId>>,
    ) -> Self {
        let mut collector = IntCollector::new(allow_opaque_apps);
        collector.record_touches = super::TouchLog::On;
        let keys = lit_terms.len();
        Self {
            policy,
            lit_terms,
            collector,
            global_symbols: Vec::new(),
            global_opaque: Vec::new(),
            cache: vec![None; keys],
            cached_literals: 0,
            assembly: Assembly::default(),
        }
    }

    /// The policy this decider was built with.
    #[must_use]
    pub fn policy(&self) -> LiaWarmPolicy {
        self.policy
    }

    /// The polarity-applied term for a literal key, if the caller registered one.
    #[must_use]
    pub fn term_of(&self, key: usize) -> Option<TermId> {
        self.lit_terms.get(key).copied().flatten()
    }

    /// Decides the conjunction of `live` — literal keys, in trail order.
    ///
    /// The verdict is the offline decider's verdict on the same conjunction, and
    /// a `sat` carries a model that has been replayed against `arena` and the
    /// live terms: the same trust anchor `lia_simplex_capped` applies, not a
    /// weaker one.
    ///
    /// # Errors
    ///
    /// [`SolverError::Unsupported`] for a literal outside conjunctive linear
    /// integer arithmetic, or [`SolverError::Backend`] on a `sat` replay failure.
    pub fn check(
        &mut self,
        arena: &TermArena,
        live: &[usize],
        node_cap: u64,
        deadline: Option<Instant>,
    ) -> Result<CheckResult, SolverError> {
        bump(Slot::Checks, 1);
        let result = self.check_inner(arena, live, node_cap, deadline);
        bump(
            match &result {
                Ok(CheckResult::Unsat) => Slot::VerdictUnsat,
                Ok(CheckResult::Sat(_)) => Slot::VerdictSat,
                Ok(CheckResult::Unknown(_)) => Slot::VerdictUnknown,
                Err(_) => Slot::VerdictError,
            },
            1,
        );
        result
    }

    fn check_inner(
        &mut self,
        arena: &TermArena,
        live: &[usize],
        node_cap: u64,
        deadline: Option<Instant>,
    ) -> Result<CheckResult, SolverError> {
        if !self.policy.warm {
            self.assembly.clear();
            bump(Slot::Rebuilds, 1);
            bump(Slot::AssemblyPolicyCold, 1);
        }
        if self.assemble(arena, live, deadline)?.is_none() {
            return Ok(lia_collection_timeout());
        }
        // An `i128` overflow while linearizing poisons the system; degrade to a
        // graceful `unknown` before any constraint is interpreted, exactly as the
        // cold path does (never a wrong verdict).
        if self.assembly.overflow() {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::ResourceLimit,
                detail: "lia simplex: i128 overflow while linearizing the integer constraints"
                    .to_owned(),
            }));
        }
        if self.assembly.trivially_unsat() {
            return Ok(CheckResult::Unsat);
        }
        let nvars = self.assembly.local_to_global.len();
        let has_opaque_vars = self.assembly.has_opaque();
        let live_constraints = self.assembly.constraints.len();
        bump(Slot::ConstraintsLive, live_constraints as u64);
        bump(Slot::ColumnsLive, nvars as u64);
        // The engines take the system by `&mut` because branch-and-bound uses it
        // as a backtracking stack — it pushes a bound constraint, recurses and
        // pops it on every path out. Handing them the assembly directly is what
        // keeps a check proportional to the trail delta; the assertion below is
        // the standing check that the stack discipline really is symmetric, so a
        // future edit cannot silently leave a branch bound behind for the next
        // check to inherit as part of its "shared prefix".
        let outcome =
            decide_int_constraints(&mut self.assembly.constraints, nvars, node_cap, deadline);
        assert_eq!(
            self.assembly.constraints.len(),
            live_constraints,
            "the offline engines left the assembled system a different length; a warm prefix \
             must never inherit another check's branch bounds"
        );
        match outcome {
            LiaBnb::Unsat => Ok(CheckResult::Unsat),
            LiaBnb::Unknown(cause) => Ok(lia_bnb_undecided(cause, node_cap)),
            LiaBnb::Sat(values) => {
                if has_opaque_vars {
                    return Ok(CheckResult::Unknown(UnknownReason {
                        kind: UnknownKind::Incomplete,
                        detail: "opaque integer UF abstraction is satisfiable; SAT model lifting \
                                 is owned by the UFLIA backend"
                            .to_owned(),
                    }));
                }
                let mut model = Model::new();
                let mut assignment = axeyum_ir::Assignment::new();
                for (local, &global) in self.assembly.local_to_global.iter().enumerate() {
                    let Some(symbol) = self.global_symbols[global] else {
                        continue;
                    };
                    let value = values[local];
                    debug_assert!(
                        value.is_integer(),
                        "branch-and-bound returned a fractional value"
                    );
                    model.set(symbol, Value::Int(value.numerator()));
                    assignment.set(symbol, Value::Int(value.numerator()));
                }
                // The shared trust anchor: a `sat` is only a `sat` once the model
                // satisfies the ORIGINAL terms under the ground evaluator.
                for &key in live {
                    let Some(term) = self.term_of(key) else {
                        return Err(SolverError::Unsupported(format!(
                            "QF_LIA: the warm decider has no term registered for literal key                              {key}"
                        )));
                    };
                    match eval(arena, term, &assignment) {
                        Ok(Value::Bool(true)) => {}
                        Ok(_) => {
                            return Err(SolverError::Backend(format!(
                                "warm lia simplex sat model replay failed: literal term #{} not \
                                 satisfied",
                                term.index()
                            )));
                        }
                        Err(error) => {
                            return Err(SolverError::Backend(format!(
                                "warm lia simplex sat model replay error on literal term #{}: \
                                 {error}",
                                term.index()
                            )));
                        }
                    }
                }
                Ok(CheckResult::Sat(model))
            }
        }
    }

    /// Brings the assembly in line with `live`. `Ok(None)` means the deadline
    /// passed during collection, and the caller reports a collection timeout.
    fn assemble(
        &mut self,
        arena: &TermArena,
        live: &[usize],
        deadline: Option<Instant>,
    ) -> Result<Option<()>, SolverError> {
        let shared = self
            .assembly
            .keys
            .iter()
            .zip(live)
            .take_while(|(a, b)| a == b)
            .count();
        let previous = self.assembly.keys.len();
        if self.policy.warm {
            let reason = if shared == previous && shared == live.len() {
                AssemblyReason::Unchanged
            } else if shared == 0 {
                AssemblyReason::ColdStart
            } else if shared == previous {
                AssemblyReason::Extended
            } else if shared == live.len() {
                AssemblyReason::Shortened
            } else {
                AssemblyReason::Diverged
            };
            let removed = previous - shared;
            let added = live.len() - shared;
            bump(ASSEMBLY_SLOTS[reason.slot()], 1);
            if matches!(reason, AssemblyReason::ColdStart) {
                bump(Slot::Rebuilds, 1);
            } else {
                bump(Slot::WarmUpdates, 1);
            }
            bump(Slot::DeltaKept, shared as u64);
            bump(Slot::DeltaRemoved, removed as u64);
            bump(Slot::DeltaAdded, added as u64);
        } else {
            bump(Slot::DeltaAdded, live.len() as u64);
        }
        self.assembly.truncate(shared);
        for (offset, &key) in live[shared..].iter().enumerate() {
            if past_deadline(deadline) {
                // A partially-assembled system must never be reused as a prefix.
                self.assembly.clear();
                return Ok(None);
            }
            let entry = match self.entry(arena, key, deadline) {
                Ok(Some(entry)) => entry,
                Ok(None) => {
                    self.assembly.clear();
                    return Ok(None);
                }
                Err(error) => {
                    self.assembly.clear();
                    return Err(error);
                }
            };
            let copied = self.assembly.append(key, &entry, shared + offset);
            bump(Slot::ConstraintsCopied, copied as u64);
            self.stash(key, entry);
        }
        Ok(Some(()))
    }

    /// The cached — or freshly collected — entry for one literal key.
    ///
    /// Returns the entry by value so the borrow of `self.cache` ends before the
    /// assembly is mutated; [`Self::stash`] puts it back. A clone of one
    /// literal's constraints is the price of that, and it is bounded by the
    /// literal, never by the live set.
    fn entry(
        &mut self,
        arena: &TermArena,
        key: usize,
        deadline: Option<Instant>,
    ) -> Result<Option<LiteralEntry>, SolverError> {
        if let Some(entry) = self.cache.get(key).and_then(Option::as_ref) {
            bump(Slot::LiteralCacheHits, 1);
            return Ok(Some(entry.clone()));
        }
        bump(Slot::LiteralCollections, 1);
        let Some(term) = self.term_of(key) else {
            // Fail closed. Treating a key with no term as contributing nothing
            // would silently drop a live literal from the conjunction — a weaker
            // system, which is how a warm path turns an `unsat` into a `sat`. The
            // caller registers a term for every key it can assert, so this is a
            // contract violation, not an input the decider should absorb.
            return Err(SolverError::Unsupported(format!(
                "QF_LIA: the warm decider has no term registered for literal key {key}"
            )));
        };
        // The persistent collector keeps only its column space across literals;
        // everything per-assertion is reset here, so one literal's collection can
        // never read another's residue.
        self.collector.constraints.clear();
        self.collector.touch_log.clear();
        self.collector.trivially_unsat = false;
        self.collector.overflow = false;
        self.collector.current_origin = 0;
        let vars_before = self.collector.vars.len();
        let columns_before = self.collector.next_var;
        let opaque_before = self.collector.opaque_var_index.len();
        let completed = self
            .collector
            .collect_within(arena, term, false, deadline)?;
        if !completed {
            self.collector.constraints.clear();
            self.collector.touch_log.clear();
            return Ok(None);
        }
        self.sync_global_tables(vars_before, columns_before, opaque_before);
        let mut touched: Vec<usize> = Vec::with_capacity(self.collector.touch_log.len());
        for &global in &self.collector.touch_log {
            if !touched.contains(&global) {
                touched.push(global);
            }
        }
        let has_opaque = touched.iter().any(|&g| self.global_opaque[g]);
        let mut constraints = std::mem::take(&mut self.collector.constraints);
        tighten_int_constraints(&mut constraints);
        let entry = LiteralEntry {
            constraints,
            touched,
            trivially_unsat: self.collector.trivially_unsat,
            overflow: self.collector.overflow,
            has_opaque,
        };
        self.collector.touch_log.clear();
        Ok(Some(entry))
    }

    /// Files an entry in the cache, subject to
    /// [`LiaWarmPolicy::max_cached_literals`].
    fn stash(&mut self, key: usize, entry: LiteralEntry) {
        if key >= self.cache.len() || self.cache[key].is_some() {
            return;
        }
        if self.cached_literals >= self.policy.max_cached_literals {
            bump(Slot::LiteralCacheEvicted, 1);
            return;
        }
        self.cached_literals += 1;
        self.cache[key] = Some(entry);
    }

    /// The system currently assembled, in the shape [`super::cold_int_system`]
    /// returns — so a test can compare the two structurally rather than settling
    /// for verdict agreement between two independently sound engines.
    #[cfg(test)]
    pub(crate) fn assembled_system(&self) -> super::ColdIntSystem {
        super::ColdIntSystem {
            constraints: self.assembly.constraints.clone(),
            nvars: self.assembly.local_to_global.len(),
            has_opaque_vars: self.assembly.has_opaque(),
            trivially_unsat: self.assembly.trivially_unsat(),
            overflow: self.assembly.overflow(),
        }
    }

    /// Grows the global column tables to cover the columns the last collection
    /// allocated.
    ///
    /// Columns are allocated in increasing order, and each allocation either
    /// pushes a symbol onto `IntCollector::vars` or inserts into
    /// `IntCollector::opaque_var_index`. So among the new columns in ascending
    /// order, the ones that are not opaque correspond, in order, to the symbols
    /// appended to `vars` — which is why this is `O(new columns)` and not a scan
    /// of the whole symbol table.
    fn sync_global_tables(
        &mut self,
        vars_before: usize,
        columns_before: usize,
        opaque_before: usize,
    ) {
        let total = self.collector.next_var;
        if total == columns_before {
            return;
        }
        self.global_symbols.resize(total, None);
        self.global_opaque.resize(total, false);
        if self.collector.opaque_var_index.len() != opaque_before {
            for &column in self.collector.opaque_var_index.values() {
                if column >= columns_before {
                    self.global_opaque[column] = true;
                }
            }
        }
        let mut symbol = vars_before;
        for column in columns_before..total {
            if !self.global_opaque[column] {
                self.global_symbols[column] = Some(self.collector.vars[symbol]);
                symbol += 1;
            }
        }
        debug_assert_eq!(
            symbol,
            self.collector.vars.len(),
            "new columns and newly appended symbols must pair up one to one"
        );
    }
}

#[cfg(test)]
mod tests;
