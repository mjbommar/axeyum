//! A proof-producing pure-Rust CDCL SAT core (ADR-0012).
//!
//! Conflict-driven clause learning with **1-UIP** conflict analysis and
//! **two-watched-literal** propagation. Every learned clause is RUP by
//! construction, so the sequence of learned clauses is a valid DRAT proof; on
//! `unsat` the empty clause is derived. The proof is verified by
//! [`crate::check_drat`], so `unsat` is sound regardless of bugs in this
//! (untrusted) search — the project's "untrusted fast search, trusted small
//! checking" identity, realized for `unsat`.
//!
//! A conflict budget bounds the search so it can never hang. Since ADR-1703
//! this core is THE SAT engine under every shipping path; the former
//! `rustsat-batsat` adapter survives only behind the `batsat-reference`
//! feature as a measurement yardstick, never as a route.

// Monotonic clock: on wasm32 the browser has no `std` clock, so use `web-time`'s
// drop-in `Instant` (ADR-0017). Native targets use the std clock.
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;

#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use crate::clause_db_policy::{ClauseDbPolicy, KeepReason, Tier, WatchSweep};
use crate::drat::{DratSink, DratStep, ProofSinkError, VecProofSink};
use crate::inprocess::{InprocessOptions, InprocessStats, inprocess_into};
use crate::phase_policy::{
    ModeSchedule, PhasePolicy, RephaseAction, RestartPolicy, RestartSchedule,
};
use crate::{CnfAssignment, CnfFormula, CnfLit, CnfVar};

pub mod theory;

/// The ADR-1704 two-stream artifact a theory-driven refutation produces.
pub mod refutation;

use theory::{
    ExplanationId, FinalCheckOutcome, NativeTheory, NullTheory, PropagationQueue, TheoryExplanation,
};

pub use refutation::{TheoryRefutation, TheoryRefutationCheck, TheoryRefutationError};

/// Default maximum conflicts before the proof-producing core gives up.
pub const DEFAULT_PROOF_SAT_CONFLICT_LIMIT: usize = 2_000_000;

/// Default number of conflicts between progress-sink polls, when a sink is
/// installed (see [`ProofSearchProgress`]). A conflict-count cadence — not a
/// wall-clock timer — keeps polling deterministic w.r.t. the search, mirroring
/// `DEADLINE_CHECK_INTERVAL`'s rationale (private to this module): the search
/// trajectory up to any
/// point does not depend on when the sink happens to be polled, only on
/// whether it is installed at all (and it never is, on the default path).
pub const DEFAULT_PROGRESS_CONFLICT_INTERVAL: usize = 5_000;

/// How many conflicts elapse between wall-clock deadline checks. A fixed
/// conflict cadence (not a per-decision clock read) keeps the deadline test
/// deterministic w.r.t. the search and cheap.
const DEADLINE_CHECK_INTERVAL: usize = 1_024;

/// Defense-in-depth ceiling on search-loop iterations **when a theory is
/// attached**, ported from `CdclT`'s `DEFAULT_STEP_BUDGET`.
///
/// The Boolean half of this core cannot spin: every iteration either conflicts
/// (bounded by `max_conflicts`) or assigns a variable, and both budgets are
/// finite. A *theory* can. The theories this core will drive are incomplete and
/// non-monotone -- `StringTheory` re-runs its refuter per assert and may report
/// at assert `k` a conflict it missed at `k-1` -- and a theory that registers an
/// atom or propagates a literal on every round would otherwise loop with no
/// conflict to count. Exhausting this budget is *sound*: the search abandons
/// with the undecided [`SearchOutcome::Interrupted`], never a verdict.
///
/// Compiled out entirely for [`NullTheory`] (`HAS_THEORY == false`), so no
/// shipping SAT path pays for it or can be stopped by it.
const THEORY_STEP_BUDGET: usize = 16_000_000;

/// VSIDS activity decay: each conflict `var_inc` is divided by this, so older
/// activity bumps decay geometrically relative to fresh ones (the `MiniSat`
/// scheme).
const VSIDS_DECAY: f64 = 0.95;
/// Rescale all activities (and `var_inc`) by this when any exceeds the cap, to
/// avoid `f64` overflow without changing their relative order.
const VSIDS_RESCALE: f64 = 1e-100;
/// Activity ceiling that triggers a rescale.
const VSIDS_RESCALE_LIMIT: f64 = 1e100;
/// Conflict-interval unit multiplied by the Luby value to set each restart's
/// length.
const LUBY_UNIT: usize = 100;

/// Clause-activity decay: each conflict the clause bump increment grows by
/// `1/CLAUSE_DECAY`, so older clause bumps decay relative to fresh ones.
const CLAUSE_DECAY: f64 = 0.999;
/// Rescale all clause activities (and `cla_inc`) when one exceeds this cap, to
/// avoid `f64` overflow without changing their relative order.
const CLAUSE_RESCALE_LIMIT: f64 = 1e20;
/// Multiplier applied on a clause-activity rescale.
const CLAUSE_RESCALE: f64 = 1e-20;

/// EMA glue restart (Glucose/CaDiCaL, T1.3.2). The **fast** exponential moving
/// average of learned-clause LBD (glue) reacts to recent conflicts; the **slow**
/// average is the long-run baseline. A restart is forced when the fast average
/// exceeds the slow one by [`RESTART_MARGIN`] — recent search is producing
/// higher-LBD (less reusable) clauses, so the current decision prefix is
/// unproductive and worth abandoning. `alpha = 2^-5` (fast) and `2^-14` (slow) are
/// the standard smoothing rates; all-`f64` so the schedule is fully deterministic.
const GLUE_EMA_FAST_ALPHA: f64 = 0.031_25; // 2^-5
const GLUE_EMA_SLOW_ALPHA: f64 = 6.103_515_625e-5; // 2^-14
/// Force a restart when `glue_fast > RESTART_MARGIN * glue_slow`.
const RESTART_MARGIN: f64 = 1.25;
/// Blocking restarts (Glucose): suppress an otherwise-due restart while the trail
/// is far deeper than its slow average — the search is close to a model and
/// restarting would throw that progress away. `trail_len > BLOCKING_MARGIN *
/// trail_slow` blocks.
const TRAIL_EMA_ALPHA: f64 = 6.103_515_625e-5; // 2^-14
const BLOCKING_MARGIN: f64 = 1.40;
/// Minimum conflicts between two EMA restarts (anti-thrash), and the conflict
/// warmup before the EMA rule engages (so the slow average is meaningful).
const MIN_RESTART_INTERVAL: usize = 50;
const EMA_RESTART_WARMUP: usize = 100;

/// The `i`-th term (1-indexed) of the Luby sequence `1,1,2,1,1,2,4,1,…`, used to
/// space restarts (Knuth's reluctant-doubling formulation, iterative).
fn luby(mut i: u64) -> u64 {
    let mut k = 1u64;
    loop {
        let pow = 1u64 << k; // 2^k
        if i == pow - 1 {
            return 1u64 << (k - 1); // 2^(k-1)
        }
        let half = 1u64 << (k - 1); // 2^(k-1)
        if half <= i && i < pow - 1 {
            i = i - half + 1;
            k = 1;
        } else {
            k += 1;
        }
    }
}

/// Outcome of [`solve_with_drat_proof`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofSolveOutcome {
    /// Satisfiable, with a model over the formula's variables.
    Sat(CnfAssignment),
    /// Unsatisfiable, with a DRAT proof verifiable by [`crate::check_drat`].
    Unsat(Vec<DratStep>),
    /// The conflict budget was exhausted before a result was reached.
    ResourceOut,
    /// The wall-clock deadline passed before a result was reached. Like
    /// [`ProofSolveOutcome::ResourceOut`] this is an *undecided* verdict — the
    /// core never returns `sat`/`unsat` by timeout, so a primary search using
    /// this core can map it to `unknown` without any soundness risk.
    Interrupted,
}

/// Outcome of [`solve_with_drat_proof_streaming`].
///
/// Mirrors [`ProofSolveOutcome`] except that `Unsat` carries nothing: the proof
/// went to the caller's [`DratSink`] as it was derived, so there is no `Vec` to
/// return. The extra variant is [`StreamingProofOutcome::SinkFailed`] — a sink
/// that could not accept a step, which is an *undecided* result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StreamingProofOutcome {
    /// Satisfiable, with a model over the formula's variables.
    Sat(CnfAssignment),
    /// Unsatisfiable. The DRAT proof — including its deletion steps and the
    /// final empty clause — was emitted to the sink, in the same order
    /// [`ProofSolveOutcome::Unsat`] would have returned it, and can be verified
    /// by [`crate::check_drat`] / [`crate::check_drat_streaming`].
    Unsat,
    /// The conflict budget was exhausted before a result was reached.
    ResourceOut,
    /// The wall-clock deadline passed before a result was reached (an
    /// *undecided* verdict; see [`ProofSolveOutcome::Interrupted`]).
    Interrupted,
    /// The sink refused a proof step (a full disk, a closed pipe). The search is
    /// abandoned at that point and **no verdict is reported**: a refutation
    /// whose proof could not be recorded is not a checked `unsat`, so this is an
    /// undecided result, never a wrong one. Nothing is panicked and no partial
    /// verdict leaks — the steps already accepted by the sink are a prefix of
    /// the proof and are not, on their own, a refutation.
    SinkFailed(ProofSinkError),
}

/// A point-in-time, cumulative-since-start snapshot of a proof-producing
/// search, handed to an optional callback so a long-running certificate run is
/// observable (see the motivating incident: a `neg-fp16-add-monotone-rne.smt2`
/// DRAT run went for 5 h 59 min with zero bytes of output before being
/// reaped, and the same query decides in 11.5 s through the non-certifying
/// path — only certificate production runs unboundedly). Every field is a
/// running total, not a delta, so a watcher can compute a rate
/// (`conflicts as f64 / elapsed.as_secs_f64()`, `proof_bytes as f64 /
/// elapsed.as_secs_f64()`) from a single snapshot and state a falsifiable
/// expectation ("at this rate it finishes by X or it does not") rather than
/// just observe that something is still moving.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ProofSearchProgress {
    /// Conflicts encountered so far.
    pub conflicts: usize,
    /// Live (non-deleted) learned clauses right now — distinct from `proof_steps`,
    /// which counts every `add`/`delete` step ever emitted, including ones
    /// `reduce_db` has since deleted.
    pub learned_clauses: usize,
    /// Total DRAT steps emitted so far (every `add_clause` and `delete_clause`
    /// call made to the sink).
    pub proof_steps: usize,
    /// Exact byte length the emitted steps would occupy in the standard DRAT
    /// text format ([`crate::write_drat`] / [`crate::TextProofSink`]) — computed
    /// from the same literal counts without allocating or formatting a string.
    pub proof_bytes: u64,
    /// Wall-clock time since this search began.
    pub elapsed: Duration,
}

/// Per-search event counts for the native CDCL core — the decomposition of
/// per-conflict cost that
/// [the 2026-09-05 native-core-vs-Kissat search-statistics note][note] named as
/// its own largest gap:
///
/// > **The native core's own time breakdown is not measured at all** — no
/// > decision counter, no propagation counter, no restart counter exists in
/// > [`ProofSearchProgress`] to compare against Kissat's `search%`/`probe%`
/// > split on the native side.
///
/// [note]: https://github.com/../docs/research/11-design-review/2026-09-05-native-core-vs-kissat-search-stats.md
///
/// Every field is a plain event count, never a time: this type deliberately
/// carries no clock reads, so collecting it cannot perturb the thing it
/// measures the way `NativeLayerStats`'s per-stage `Instant::now()` pairs can.
/// Counting is **opt in** — [`solve_with_drat_proof_counted`] and the
/// progress-sink entry points enable it, every other entry point leaves the
/// counters at zero and never executes an increment.
///
/// Counting does not change the search: no field of this struct is read by any
/// branch of the search loop, so the trajectory, the verdict and the emitted
/// DRAT stream are identical whether it is enabled or not (asserted by
/// `tests::counting_does_not_change_the_verdict_or_the_proof`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SearchCounters {
    /// Conflicts analysed (the denominator of every per-conflict rate).
    pub conflicts: u64,
    /// Branching decisions taken by `pick_branch` (excludes assumptions).
    pub decisions: u64,
    /// Literals assigned by unit propagation (excludes decisions, assumptions
    /// and level-zero units) — the standard "propagations" statistic that
    /// `kissat -s` and `cadical -v` both report.
    pub propagations: u64,
    /// Restarts performed.
    pub restarts: u64,
    /// `reduce_db` rounds performed.
    pub reductions: u64,
    /// **Watch entries examined** in `propagate`: one per `Watch` inspected in
    /// a literal's watch list, whether or not the clause behind it was
    /// dereferenced. This is the size of the hottest memory stream in the
    /// solver.
    pub watch_visits: u64,
    /// **Watch entries whose clause was dereferenced**: the blocking literal
    /// was not true, so the clause's arena slice had to be read. The
    /// complement (`watch_visits - clause_visits`) is what the blocking-literal
    /// optimisation saves.
    pub clause_visits: u64,
    /// **Watch entries examined whose clause is binary.** A subset of
    /// [`SearchCounters::watch_visits`], so `watch_visits -
    /// binary_watch_visits` is the long-clause traffic. This is the number that
    /// says whether the binary special case is worth having on a given formula
    /// — a formula whose watch traffic is 5% binary cannot be helped by it, and
    /// reporting the ratio is the honest way to find that out.
    pub binary_watch_visits: u64,
    /// **Arena dereferences the binary watch layout avoided.** A binary watch
    /// that missed the blocking-literal fast path is decided from the watch
    /// alone; under the pre-2026-09 layout every one of these read
    /// `headers[cid]`, read (and sometimes wrote) the arena, and ran an empty
    /// replacement scan. So this counter is exactly the reduction in
    /// [`SearchCounters::clause_visits`] against that layout, and it is the
    /// quantity the change is *for*.
    pub binary_arena_derefs_avoided: u64,
    /// Watches moved to a different literal's list (a new non-false literal was
    /// found). Each is a `push` onto another `Vec<Watch>`.
    pub watch_relocations: u64,
    /// Antecedent clauses walked by `analyze` — resolution steps, summed over
    /// all conflicts. `resolutions / conflicts` is the mean 1-UIP chain length.
    pub resolutions: u64,
    /// **Bytes of the per-conflict `seen` array `analyze` allocates and
    /// zeroes**, summed over all conflicts. `analyze` opens with
    /// `vec![false; self.assign.len()]`, so this is `conflicts x variables` and
    /// is *independent of how many variables the conflict actually touches*.
    /// Named as its own counter because it is the one per-conflict cost in this
    /// core that scales with the **formula**, not with the conflict.
    pub analyze_mark_bytes: u64,
    /// Reason-chain steps taken by `lit_redundant` during recursive learned-clause
    /// minimization (one per literal popped off its work stack).
    pub redundancy_steps: u64,

    // --- Clause-database policy instrumentation (see `crate::clause_db_policy`).
    // These describe the *lifetime* policy, which is the thing a tuning lane
    // needs to see and which nothing in this core previously exposed: a policy
    // nobody can observe cannot be tuned, and cannot be shown to be doing
    // anything at all.
    /// Times a learned clause's `used` counter was refreshed to
    /// `clause_db_policy::MAX_USED` — once per resolution through a learned
    /// clause, plus once per clause at learning. This is the numerator of the
    /// lifetime signal that replaced clause activity.
    pub clause_used_marks: u64,
    /// Learned clauses whose glue was recomputed on resolution and found to be
    /// *smaller* than the recorded value, promoting the clause toward tier1.
    /// Zero when `promote_on_use` is off.
    pub clause_promotions: u64,
    /// Times the dynamic tier boundaries were recomputed from the used-glue
    /// histogram (a doubling conflict schedule, so this grows like
    /// `log2(conflicts)` until the interval caps).
    pub tier_recomputes: u64,
    /// The `tier1` boundary at the most recent recomputation.
    pub tier1_limit_last: u32,
    /// The `tier2` boundary at the most recent recomputation.
    pub tier2_limit_last: u32,
    /// Sum of the `tier1` boundary over every recomputation. Divided by
    /// [`SearchCounters::tier_recomputes`] this is the mean boundary over the
    /// run — the cheapest clock-free way to see the boundary move, which is the
    /// whole claim of the dynamic-boundary change.
    pub tier1_limit_sum: u64,
    /// Sum of the `tier2` boundary over every recomputation.
    pub tier2_limit_sum: u64,
    /// Live learned clauses classified into tier1 at reduce time, summed over
    /// rounds. The three tier counters plus
    /// [`SearchCounters::reduce_locked`] and
    /// [`SearchCounters::reduce_too_short`] partition every clause examined.
    pub reduce_tier1_seen: u64,
    /// Live learned clauses classified into tier2 at reduce time, summed over
    /// rounds.
    pub reduce_tier2_seen: u64,
    /// Live learned clauses classified into tier3 at reduce time, summed over
    /// rounds.
    pub reduce_tier3_seen: u64,
    /// Clauses a reduce round kept because they were tier1 and used since the
    /// previous round.
    pub reduce_kept_tier1: u64,
    /// Clauses a reduce round kept because they were tier2 and within their
    /// one round of grace.
    pub reduce_kept_tier2: u64,
    /// Clauses a reduce round kept because they were the reason for an assigned
    /// literal (locked).
    pub reduce_locked: u64,
    /// Clauses a reduce round skipped as too short to delete (binaries).
    pub reduce_too_short: u64,
    /// Deletion candidates a reduce round produced, summed over rounds.
    pub reduce_candidates: u64,
    /// Clauses actually deleted, summed over rounds. Each one emitted a DRAT
    /// deletion step, so this is also the number of `d` lines the proof gained
    /// from reduction.
    pub reduce_deleted: u64,
    /// Clause headers a reduce round examined, summed over rounds — the cost
    /// of the candidate scan.
    pub reduce_headers_scanned: u64,
    /// Clause headers a reduce round skipped by starting at
    /// `first_reducible` instead of at clause 0, summed over rounds. Against
    /// [`SearchCounters::reduce_headers_scanned`] this is what the sweep-start
    /// saves; a large value means the database is mostly input clauses or
    /// mostly tombstones, both of which the old scan walked every round.
    pub reduce_headers_skipped: u64,
    /// Watch entries a reduce round walked to drop tombstoned clauses, summed
    /// over rounds — the cost of the watch-list half of a round. The
    /// pre-2026-09 rebuild walked the same entries *and* re-read a header and
    /// two arena cells per live clause.
    pub reduce_watch_entries_scanned: u64,
    /// Reduce rounds that deleted nothing because the keep rule protected the
    /// whole database. Nonzero here means the size-triggered schedule is being
    /// held off by the backoff rather than doing work, and the tier boundaries
    /// are probably too generous for this formula.
    pub reduce_empty_rounds: u64,
    /// Fresh high-water marks recorded for the *target* phase (the one restarts
    /// re-descend into). Under a released ratchet this keeps growing all run;
    /// under a pinned one it stops early, which is exactly the symptom that
    /// motivated the reset.
    pub target_phase_snapshots: u64,
    /// Fresh high-water marks recorded for the long-run *best* phase archive.
    pub best_phase_snapshots: u64,
    /// Times the target-phase high-water mark was reset so the ratchet could
    /// release. Zero means the target is a monotone mark that never releases.
    pub target_phase_resets: u64,
    /// Rephases performed (a scheduled reinstallation of a whole phase vector),
    /// as distinct from the per-restart copy of the target phase.
    pub rephases: u64,
    /// Restart-time rephase opportunities the mode gate refused because the
    /// search was in focused mode.
    ///
    /// This is the *observation* that the rephase confinement is real. The
    /// rephase COUNT is not: `PhasePolicy::should_rephase` is a threshold that
    /// stays true until it fires, so confining rephases to stable mode defers
    /// them rather than dropping them, and both arms of an A/B end up rephasing
    /// the same number of times. Zero whenever the gate is off, so deleting the
    /// gate makes this read zero.
    pub rephase_deferrals: u64,
    /// Stable/focused mode switches performed. Zero under every policy that
    /// does not switch, which is all of them by default.
    ///
    /// A scalar count is the summary; the *schedule* — which mode, at which
    /// conflict and tick count — is [`crate::phase_policy::ModeSchedule`], read
    /// from [`solve_with_drat_proof_mode_traced`]. Both exist because this
    /// counter alone cannot distinguish a schedule that alternates on the
    /// intended budget from one that alternates on the wrong one.
    pub mode_switches: u64,
}

impl SearchCounters {
    /// Watch entries examined per conflict — the propagation work the search
    /// paid for each conflict it learned from. Zero when nothing was counted.
    #[must_use]
    pub fn watch_visits_per_conflict(&self) -> f64 {
        if self.conflicts == 0 {
            return 0.0;
        }
        #[allow(clippy::cast_precision_loss)]
        {
            self.watch_visits as f64 / self.conflicts as f64
        }
    }

    /// Fraction of examined watches whose clause is binary. Zero when nothing
    /// was counted. This is the ceiling on what the binary watch layout can do
    /// for a formula: no arena access it removes lies outside this population.
    #[must_use]
    pub fn binary_watch_visit_rate(&self) -> f64 {
        if self.watch_visits == 0 {
            return 0.0;
        }
        #[allow(clippy::cast_precision_loss)]
        {
            self.binary_watch_visits as f64 / self.watch_visits as f64
        }
    }

    /// Fraction of examined watches whose clause had to be dereferenced — the
    /// blocking literal's **miss** rate. Lower is better; a high value means
    /// the blocker cache is not paying.
    #[must_use]
    pub fn clause_deref_rate(&self) -> f64 {
        if self.watch_visits == 0 {
            return 0.0;
        }
        #[allow(clippy::cast_precision_loss)]
        {
            self.clause_visits as f64 / self.watch_visits as f64
        }
    }
}

/// Exact byte length [`crate::write_drat`] / [`crate::TextProofSink`] would
/// produce for one step with these literals: mirrors the private
/// `push_step_text` format (an optional `"d "` prefix, one space-terminated
/// DIMACS integer per literal, a trailing `"0\n"`) without allocating a
/// string. Used only to grow [`ProofSearchProgress::proof_bytes`] when a
/// progress sink is installed — never on the hot path otherwise.
fn step_text_bytes(delete: bool, lits: &[CnfLit]) -> u64 {
    let mut bytes: u64 = u64::from(delete) * 2; // "d "
    for lit in lits {
        let value = lit.dimacs();
        let mut n = value.unsigned_abs();
        let mut digits: u64 = 1;
        while n >= 10 {
            n /= 10;
            digits += 1;
        }
        bytes += digits + u64::from(value < 0) + 1; // digits + optional '-' + trailing space
    }
    bytes + 2 // "0\n"
}

/// Solves `formula` with the proof-producing CDCL core.
pub fn solve_with_drat_proof(formula: &CnfFormula) -> ProofSolveOutcome {
    solve_with_drat_proof_within(formula, None)
}

/// Solves `formula` with the proof-producing CDCL core, stopping early if the
/// optional wall-clock `deadline` passes.
///
/// `deadline` is checked on a deterministic conflict cadence (every
/// `DEADLINE_CHECK_INTERVAL` conflicts), so the search trajectory up to the
/// stopping point is identical to the unbounded run — only *whether* it stops is
/// time-dependent. On expiry the core returns [`ProofSolveOutcome::Interrupted`],
/// an undecided verdict; it never returns `sat`/`unsat` by timeout.
///
/// [`solve_with_drat_proof`] is the `deadline = None` (proof-revalidator) entry.
pub fn solve_with_drat_proof_within(
    formula: &CnfFormula,
    deadline: Option<Instant>,
) -> ProofSolveOutcome {
    solve_with_drat_proof_with_limits(formula, deadline, DEFAULT_PROOF_SAT_CONFLICT_LIMIT)
}

/// Solves `formula` with explicit wall-clock and conflict limits.
///
/// `max_conflicts` is deterministic for a fixed formula and solver build.
/// Exceeding it returns [`ProofSolveOutcome::ResourceOut`], never a guessed
/// verdict. A level-zero contradiction may be decided without consuming a
/// conflict from this budget — **except** at `max_conflicts == 0`, which admits
/// no search at all and always returns `ResourceOut` (the "encode but do not
/// solve" contract that `resource_limit = 0` carries everywhere else in the
/// tree).
pub fn solve_with_drat_proof_with_limits(
    formula: &CnfFormula,
    deadline: Option<Instant>,
    max_conflicts: usize,
) -> ProofSolveOutcome {
    let mut sink = VecProofSink::new();
    match Cdcl::new(formula, &mut sink).solve(deadline, max_conflicts) {
        StreamingProofOutcome::Sat(model) => ProofSolveOutcome::Sat(model),
        StreamingProofOutcome::Unsat => ProofSolveOutcome::Unsat(sink.into_steps()),
        StreamingProofOutcome::ResourceOut => ProofSolveOutcome::ResourceOut,
        // `VecProofSink` is infallible, so `SinkFailed` is unreachable here. It
        // maps to the undecided verdict rather than panicking: an impossible
        // branch must not be able to produce a wrong sat/unsat, and must not be
        // able to abort a caller either.
        StreamingProofOutcome::Interrupted | StreamingProofOutcome::SinkFailed(_) => {
            ProofSolveOutcome::Interrupted
        }
    }
}

/// Solves `formula` with the proof-producing CDCL core, streaming its proof to
/// `sink`, and returns the [`SearchCounters`] the search accumulated alongside
/// the verdict.
///
/// This is the measurement entry point for the per-conflict cost decomposition:
/// propagations, decisions, restarts, watch-list traversals, blocking-literal
/// misses, resolution steps, and the bytes `analyze` zeroes per conflict. It
/// exists because the
/// [2026-09-05 native-core-vs-Kissat search-statistics comparison][note] could
/// report the native core's conflicts and wall time but had **no** propagation,
/// decision or restart counter to set against `kissat -s`'s, and so could not
/// say where a conflict's time goes.
///
/// [note]: https://github.com/../docs/research/11-design-review/2026-09-05-native-core-vs-kissat-search-stats.md
///
/// **The verdict and the DRAT stream are identical to
/// [`solve_with_drat_proof_streaming`] with the same arguments.** The counters
/// are pure output — nothing in the search reads them — so enabling them cannot
/// change a decision, a conflict, a learned clause or an emitted step. Only the
/// wall time differs, by the cost of the increments themselves.
///
/// `deadline` and `max_conflicts` behave exactly as in
/// [`solve_with_drat_proof_with_limits`]. A **fixed `max_conflicts` is the way
/// to use this for an A/B**: both arms then analyse the same number of
/// conflicts along the same trajectory, so the wall-time ratio is pure
/// per-conflict throughput and not a difference in how much search each arm did.
pub fn solve_with_drat_proof_counted(
    formula: &CnfFormula,
    deadline: Option<Instant>,
    max_conflicts: usize,
    sink: &mut impl DratSink,
) -> (StreamingProofOutcome, SearchCounters) {
    solve_with_drat_proof_counted_with_policies(
        formula,
        deadline,
        max_conflicts,
        sink,
        &SearchPolicies::default(),
    )
}

/// The search heuristics this core runs, as objects rather than constants.
///
/// The search loop asks these for every clause-database and decision-phase
/// decision it makes; swapping one changes the search's behaviour without any
/// edit to the loop. That is the point of the split, and it is what makes an
/// A/B honest: both arms are the same binary on the same trajectory code, and
/// the only difference is the policy object.
///
/// [`SearchPolicies::default`] is what every shipping entry point uses.
/// [`SearchPolicies::legacy_clause_db`] reproduces the pre-2026-09 clause
/// database (glue &le; 2 immortal, activity ranking, delete the worst half) so
/// the tier scheme can be measured against the thing it replaced.
#[derive(Debug, Clone)]
pub struct SearchPolicies {
    /// Which learned clauses survive a reduce round, in what order the rest are
    /// deleted, and how many go. Owns the dynamic tier boundaries.
    pub clause_db: ClauseDbPolicy,
    /// The target/best phase split and the rephase schedule.
    pub phase: PhasePolicy,
    /// The stable/focused mode schedule and the restart rule each mode runs.
    ///
    /// This is the production path to the glue-EMA restart schedule. Before it
    /// existed the schedule was selected by assigning `Cdcl::use_ema_restart`,
    /// a private field, and the only assignment of `true` in the crate was
    /// inside a `#[cfg(test)]` module — so the rule was implemented, sound and
    /// unreachable at the same time.
    pub restart: RestartPolicy,
}

impl Default for SearchPolicies {
    /// The shipped defaults, stated in one place.
    ///
    /// `clause_db` is the tier scheme: it replaced an activity-ranked
    /// delete-the-worst-half rule that neither reference solver uses.
    ///
    /// `phase` is deliberately still [`PhasePolicy::pinned`] — the pre-2026-09
    /// behaviour. The rephase schedule and the target-mark release are
    /// implemented and tested, but changing two heuristics at once makes
    /// neither measurable; this default flips only when the measurement says it
    /// should.
    /// `restart` is [`RestartPolicy::luby`] for the same reason: the mode
    /// schedule and the EMA rule it selects in focused mode are both new
    /// reachable surface, and the roadmap item that asked for them
    /// (`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`, 1.6) asks for
    /// a production setter and a non-regressing ratchet, not for a default
    /// flip. Flipping it also turns on [`SearchCounters`] collection, because
    /// the switch is denominated in ticks — see [`SearchPolicies::restart`].
    fn default() -> Self {
        Self {
            clause_db: ClauseDbPolicy::tiered(),
            phase: PhasePolicy::pinned(),
            restart: RestartPolicy::luby(),
        }
    }
}

impl SearchPolicies {
    /// The target/best split with the full `(B I B O)` rephase schedule.
    #[must_use]
    pub fn scheduled_phase() -> Self {
        Self {
            phase: PhasePolicy::scheduled(),
            ..Self::default()
        }
    }

    /// The target-mark release on its own, with no phase reinstallation — the
    /// minimal fix for a ratchet that never releases, isolated so it is
    /// separately attributable.
    #[must_use]
    pub fn releasing_phase() -> Self {
        Self {
            phase: PhasePolicy::releasing(),
            ..Self::default()
        }
    }

    /// The pre-2026-09 clause database, with the current phase policy.
    #[must_use]
    pub fn legacy_clause_db() -> Self {
        Self {
            clause_db: ClauseDbPolicy::legacy(),
            ..Self::default()
        }
    }

    /// Both pre-2026-09 policies: the search as it behaved before the tier
    /// scheme and the rephase schedule landed.
    #[must_use]
    pub fn legacy() -> Self {
        Self {
            clause_db: ClauseDbPolicy::legacy(),
            phase: PhasePolicy::pinned(),
            restart: RestartPolicy::luby(),
        }
    }

    /// The Glucose glue-EMA restart schedule for the whole solve, with no mode
    /// switching — the shipping way to select what `use_ema_restart = true`
    /// used to mean, and the A/B arm against [`SearchPolicies::default`].
    #[must_use]
    pub fn ema_restart() -> Self {
        Self {
            restart: RestartPolicy::ema(),
            ..Self::default()
        }
    }

    /// The reference's stable/focused arrangement: start focused with glue-EMA
    /// restarts, alternate into stable with reluctant doubling on a
    /// quadratically growing tick budget, and confine the rephase schedule to
    /// stable mode.
    ///
    /// Pair it with [`PhasePolicy::scheduled`] to exercise the rephase gate;
    /// with the default [`PhasePolicy::pinned`] there is no rephase to gate and
    /// only the restart rule alternates.
    ///
    /// **This turns [`SearchCounters`] collection on for the search**, because
    /// the switch is denominated in ticks and ticks are derived from the
    /// counters. That is the one place in this core where the counters stop
    /// being pure output: with this policy the search reads them, so
    /// "collecting counters cannot change the trajectory" holds for every other
    /// policy but not for this one. The tick total is an exact integer function
    /// of integer event counts, so the schedule stays deterministic.
    #[must_use]
    pub fn mode_switching() -> Self {
        Self {
            restart: RestartPolicy::mode_switching(),
            ..Self::default()
        }
    }
}

/// [`solve_with_drat_proof_counted`] with the search heuristics supplied
/// explicitly.
///
/// The verdict is a property of the formula, not of the policy: every policy
/// choice here only orders decisions and decides which *redundant* learned
/// clauses to forget, and both are verdict-preserving. What changes is the
/// trajectory, and therefore the counters and the DRAT stream's contents (never
/// its validity — deletions are still emitted for every clause dropped).
pub fn solve_with_drat_proof_counted_with_policies(
    formula: &CnfFormula,
    deadline: Option<Instant>,
    max_conflicts: usize,
    sink: &mut impl DratSink,
    policies: &SearchPolicies,
) -> (StreamingProofOutcome, SearchCounters) {
    let search =
        solve_with_drat_proof_mode_traced(formula, deadline, max_conflicts, sink, policies);
    (search.outcome, search.counters)
}

/// A search under an explicit policy set, together with the mode schedule it
/// followed.
#[derive(Debug, Clone, PartialEq)]
pub struct ModeTracedSearch {
    /// The verdict.
    pub outcome: StreamingProofOutcome,
    /// Search counters over the whole solve.
    pub counters: SearchCounters,
    /// Which modes the search occupied, when it switched, and on what budget.
    /// Empty and focused under a policy that does not switch.
    pub modes: ModeSchedule,
}

/// [`solve_with_drat_proof_counted_with_policies`], also returning the
/// stable/focused schedule the search followed.
///
/// # Why this exists as a separate entry point
///
/// A mode switch is easy to add and hard to observe. Every verdict-level check
/// — the corpus sweep, the `DRAT` checker, a differential fuzz — passes
/// identically whether the switch fires or is disabled, because none of them is
/// a claim about the schedule. So the schedule has to be readable, or the
/// feature is exactly the kind of unfalsifiable mechanism this repository keeps
/// finding after the fact. [`ModeSchedule::mode_sequence`] is the assertion
/// surface; [`ModeSchedule::transitions`] carries the tick and conflict counts
/// that placed each switch.
///
/// The schedule is deterministic: every quantity it reads is an integer count
/// of search events, so the same formula under the same policy produces the
/// same transition list on any host under any load.
///
/// # Reaching the span log
///
/// `axeyum-solver`'s `span_log` cannot be written from here — `axeyum-cnf` does
/// not depend on `axeyum-solver`, the dependency runs the other way. A lane
/// that wants the schedule in a span needs a solver-side route that calls this
/// entry point (or threads a [`ModeSchedule`] out of the backend that does) and
/// emits `mode_sequence()` plus each transition's `at_ticks`. Nothing in this
/// crate can do it, and no claim here says otherwise.
pub fn solve_with_drat_proof_mode_traced(
    formula: &CnfFormula,
    deadline: Option<Instant>,
    max_conflicts: usize,
    sink: &mut impl DratSink,
    policies: &SearchPolicies,
) -> ModeTracedSearch {
    let mut cdcl = Cdcl::new(formula, sink);
    cdcl.set_policies(policies);
    let (outcome, counters, modes) = cdcl.solve_counted_traced(deadline, max_conflicts);
    ModeTracedSearch {
        outcome,
        counters,
        modes,
    }
}

/// A search that ran over an inprocessed formula: the verdict, the search
/// counters, and what the reducing passes did.
///
/// Returned as a struct rather than a tuple because the third member is the one
/// a reader is most likely to skip, and it is the one that says whether the
/// verdict came from the formula the caller handed in or from a reduction of
/// it.
#[derive(Debug, Clone, PartialEq)]
pub struct InprocessedSearch {
    /// The verdict. A `Sat` model has already been lifted back through the
    /// reduction, so it is over the **caller's** variables and satisfies the
    /// **caller's** formula — nothing downstream needs to know a reduction
    /// happened.
    pub outcome: StreamingProofOutcome,
    /// Search counters, zero unless the counted entry point was used. These are
    /// counted over the **reduced** formula, which is the point: the hypothesis
    /// under test is that a smaller formula costs fewer propagations per
    /// conflict.
    pub counters: SearchCounters,
    /// What the reducing passes did, including how many `DRAT` steps they cost.
    pub inprocess: InprocessStats,
}

/// Solves `formula` with the proof-producing CDCL core after running the
/// reducing passes `options` enables, streaming **one** `DRAT` proof of the
/// **original** `formula` to `sink` — the passes' derivation first, then the
/// search's own steps (ADR-1750).
///
/// This is the entry point behind the propagation-volume experiment described in
/// [`crate::inprocess`]: the search's [`SearchCounters`] are measured over the
/// reduced formula, so `propagations / conflicts` is directly comparable against
/// the same call with [`InprocessOptions::OFF`].
///
/// # What the certificate covers
///
/// The concatenated stream verifies against the formula the caller passed in,
/// not against the reduced one. That is the whole point of routing inprocessing
/// through here rather than doing it in the caller: a solver that preprocesses
/// and then emits a proof of the preprocessed formula has quietly narrowed what
/// its certificate certifies, and nothing in the pipeline announces it.
///
/// # What is unchanged
///
/// With [`InprocessOptions::OFF`] (the default) no pass runs, no step is
/// emitted, and this is [`solve_with_drat_proof_streaming`] exactly — same
/// trajectory, same verdict, same bytes.
///
/// # `sat`
///
/// The model is lifted back through the reduction before it is returned, so it
/// is over the caller's variables and satisfies the caller's formula. Only BVE
/// makes that lift non-trivial; subsumption and vivification are
/// model-preserving.
pub fn solve_with_drat_proof_counted_inprocessed(
    formula: &CnfFormula,
    deadline: Option<Instant>,
    max_conflicts: usize,
    sink: &mut impl DratSink,
    options: InprocessOptions,
) -> InprocessedSearch {
    let reduced = match inprocess_into(formula, options, deadline, sink) {
        Ok(reduced) => reduced,
        // The sink refused a prefix step. No search runs and no verdict is
        // reported: a reduction whose derivation could not be recorded is not
        // something a later refutation may be built on. Same undecided contract
        // as `StreamingProofOutcome::SinkFailed` everywhere else.
        Err(error) => {
            return InprocessedSearch {
                outcome: StreamingProofOutcome::SinkFailed(error),
                counters: SearchCounters::default(),
                inprocess: InprocessStats::default(),
            };
        }
    };
    let (outcome, counters) =
        Cdcl::new(&reduced.formula, sink).solve_counted(deadline, max_conflicts);
    let outcome = match outcome {
        StreamingProofOutcome::Sat(model) => StreamingProofOutcome::Sat(CnfAssignment::new(
            reduced.reconstruction.extend(model.values()),
        )),
        other => other,
    };
    InprocessedSearch {
        outcome,
        counters,
        inprocess: reduced.stats,
    }
}

/// Like [`solve_with_drat_proof_counted_inprocessed`] but without the counters
/// (nothing in the search increments them), and returning the proof as a `Vec`
/// the way [`solve_with_drat_proof`] does.
///
/// The returned proof is a proof of `formula`, inprocessing prefix included.
pub fn solve_with_drat_proof_inprocessed(
    formula: &CnfFormula,
    deadline: Option<Instant>,
    max_conflicts: usize,
    options: InprocessOptions,
) -> ProofSolveOutcome {
    let mut sink = VecProofSink::new();
    let search = {
        // `VecProofSink` is infallible, so the `else` is unreachable; it maps to
        // the undecided verdict rather than panicking, so an impossible branch
        // can never become a wrong `sat`/`unsat` and never aborts a caller.
        let Ok(reduced) = inprocess_into(formula, options, deadline, &mut sink) else {
            return ProofSolveOutcome::Interrupted;
        };
        let outcome = Cdcl::new(&reduced.formula, &mut sink).solve(deadline, max_conflicts);
        match outcome {
            StreamingProofOutcome::Sat(model) => StreamingProofOutcome::Sat(CnfAssignment::new(
                reduced.reconstruction.extend(model.values()),
            )),
            other => other,
        }
    };
    match search {
        StreamingProofOutcome::Sat(model) => ProofSolveOutcome::Sat(model),
        StreamingProofOutcome::Unsat => ProofSolveOutcome::Unsat(sink.into_steps()),
        StreamingProofOutcome::ResourceOut => ProofSolveOutcome::ResourceOut,
        StreamingProofOutcome::Interrupted | StreamingProofOutcome::SinkFailed(_) => {
            ProofSolveOutcome::Interrupted
        }
    }
}

/// Solves `formula` with the proof-producing CDCL core, **streaming** the DRAT
/// proof to `sink` instead of accumulating it (ADR-0381).
///
/// The motivating measurement: the in-RAM `Vec<DratStep>` proof of a 35,858-clause
/// instance grew until the process was OOM-killed at 27.6 GiB RSS after ~2.5 h
/// (`docs/plan/claim-ledger-and-rado-frontier-2026-08-12.md`, "Product findings",
/// item 4). With a [`crate::TextProofSink`] over a file, the core's proof
/// footprint is a fixed buffer, whatever the search costs.
///
/// **The search trajectory is identical to
/// [`solve_with_drat_proof_with_limits`].** Sink calls are pure output: the same
/// decisions, conflicts, learned clauses, restarts, and reductions happen in the
/// same order, and the same steps are emitted in the same order — feeding a
/// [`crate::VecProofSink`] here reproduces the non-streaming proof exactly, and a
/// [`crate::TextProofSink`] reproduces `write_drat` of it byte for byte.
/// Determinism is a public API promise of this workspace, and the choice of sink
/// is not an input to the search.
///
/// `deadline` and `max_conflicts` behave exactly as in
/// [`solve_with_drat_proof_with_limits`] (deterministic conflict cadence for the
/// clock; never a verdict by timeout).
pub fn solve_with_drat_proof_streaming(
    formula: &CnfFormula,
    deadline: Option<Instant>,
    max_conflicts: usize,
    sink: &mut impl DratSink,
) -> StreamingProofOutcome {
    Cdcl::new(formula, sink).solve(deadline, max_conflicts)
}

/// Solves `formula` with explicit wall-clock and conflict limits, invoking
/// `progress` every `progress_interval` conflicts (and once more at the end)
/// with a cumulative [`ProofSearchProgress`] snapshot — the observability hook
/// for a certificate run long enough that elapsed time and RSS are otherwise
/// the only signals available.
///
/// **Same trajectory as [`solve_with_drat_proof_with_limits`], always.** The
/// callback is pure output, read by nothing else in the search — installing
/// one, or changing `progress_interval`, cannot change the decisions,
/// conflicts, learned clauses, restarts, reductions, or the emitted DRAT
/// proof, only when and how often this function is told about them. That
/// property is asserted directly in
/// `tests::progress_sink_does_not_change_the_verdict_or_proof`.
///
/// `progress_interval` is clamped to at least 1 (an interval of 0 would never
/// fire the modulo test).
pub fn solve_with_drat_proof_with_limits_and_progress(
    formula: &CnfFormula,
    deadline: Option<Instant>,
    max_conflicts: usize,
    progress_interval: usize,
    progress: &mut (dyn FnMut(&ProofSearchProgress) + Send),
) -> ProofSolveOutcome {
    let mut sink = VecProofSink::new();
    let outcome = Cdcl::new(formula, &mut sink)
        .with_progress(progress_interval, progress)
        .solve(deadline, max_conflicts);
    match outcome {
        StreamingProofOutcome::Sat(model) => ProofSolveOutcome::Sat(model),
        StreamingProofOutcome::Unsat => ProofSolveOutcome::Unsat(sink.into_steps()),
        StreamingProofOutcome::ResourceOut => ProofSolveOutcome::ResourceOut,
        // See `solve_with_drat_proof_with_limits`: `VecProofSink` is infallible.
        StreamingProofOutcome::Interrupted | StreamingProofOutcome::SinkFailed(_) => {
            ProofSolveOutcome::Interrupted
        }
    }
}

/// Like [`solve_with_drat_proof_streaming`], but also invokes `progress` every
/// `progress_interval` conflicts (and once more at the end) with a cumulative
/// [`ProofSearchProgress`] snapshot. See
/// [`solve_with_drat_proof_with_limits_and_progress`] for the no-behaviour-change
/// guarantee, which holds identically here.
pub fn solve_with_drat_proof_streaming_with_progress(
    formula: &CnfFormula,
    deadline: Option<Instant>,
    max_conflicts: usize,
    sink: &mut impl DratSink,
    progress_interval: usize,
    progress: &mut (dyn FnMut(&ProofSearchProgress) + Send),
) -> StreamingProofOutcome {
    Cdcl::new(formula, sink)
        .with_progress(progress_interval, progress)
        .solve(deadline, max_conflicts)
}

/// The native core's driver-side stage timings and counters — the
/// `axeyum-cnf` half of `axeyum_solver::layers::TheoryLayerStats` (plan slice
/// S7b step 1).
///
/// The solver's `CdclT` has carried these since S1b and they are what
/// `smtcomp_cli --trace` prints. Moving CDCL(T) onto this core is a swap of one
/// engine for another, and a swap is only measurable if the *same* instrument
/// reports from both sides — so this is ported before anything moves, and it
/// carries exactly the fields `CdclT` computes, with the same increment sites:
/// `analyze`'s asserting-clause branch, a theory-attributed conflict, one
/// decision, one completed `final_check`, one theory-assigned literal.
///
/// # Collection is opt-in and off by default
///
/// Every field stays at `Default` unless the search was built with
/// `Cdcl::collect_layer_stats` set, which only
/// [`solve_with_theory_and_drat_proof_traced`] does. A default run reads no
/// extra clock, so the shipping `NullTheory` trajectory and its DRAT stream are
/// untouched.
///
/// The theory-side engine counters (`simplex_pivots`, …) are deliberately
/// absent: they belong to the `TheorySolver` implementation, not to the driver,
/// and the solver-side adapter fills them from `TheorySolver::engine_counters`
/// exactly as it does today.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct NativeLayerStats {
    /// Time inside Boolean unit propagation (`Cdcl::propagate`).
    pub boolean_propagate: Duration,
    /// Time inside [`theory::NativeTheory::assert`] calls.
    pub theory_assert: Duration,
    /// Time inside [`theory::NativeTheory::propagate_into`] calls.
    pub theory_propagate: Duration,
    /// Time inside [`theory::NativeTheory::push`] / [`theory::NativeTheory::pop`].
    pub theory_push_pop: Duration,
    /// Time inside 1-UIP conflict analysis (`Cdcl::analyze`).
    pub conflict_analysis: Duration,
    /// Time inside [`theory::NativeTheory::final_check`] calls.
    pub theory_final_check: Duration,
    /// Time inside [`theory::NativeTheory::explain`] calls.
    pub theory_explain: Duration,
    /// Completed `final_check` calls — the number of times the Boolean search
    /// reached a total assignment of the branchable variables.
    pub final_checks: u64,
    /// Conflicts whose falsified clause came from the theory (an `assert`
    /// conflict, a propagation onto an already-false literal, or a
    /// `final_check` conflict) rather than from an input or learned clause.
    pub theory_conflicts: u64,
    /// Literals the driver assigned on the theory's say-so.
    pub theory_propagations: u64,
    /// Search decisions taken (heap picks, not implied assignments).
    pub decisions: u64,
    /// Asserting clauses 1-UIP analysis produced.
    pub learned_clauses: u64,
    /// Literals summed over those clauses **after** recursive minimization.
    pub learned_literals: u64,
    /// The same sum taken **before** minimization, so one run prices what
    /// minimization removed.
    pub learned_literals_before_minimization: u64,
    /// Completed restarts.
    pub restarts: u64,
}

impl NativeLayerStats {
    /// Total wall-clock across the named stages. Excludes everything the search
    /// does outside them (decision selection, trail maintenance, VSIDS bumps),
    /// exactly as `TheoryLayerStats::total` does.
    #[must_use]
    pub fn total(&self) -> Duration {
        self.boolean_propagate
            + self.theory_assert
            + self.theory_propagate
            + self.theory_push_pop
            + self.conflict_analysis
            + self.theory_final_check
            + self.theory_explain
    }
}

/// How many theory search-loop iterations elapse between two mirror flushes
/// (see [`NativeLayerStatsMirror`]). The same cadence as
/// `DEADLINE_CHECK_INTERVAL`, and for the same reason: a fixed iteration count,
/// never a clock read, so the flush cannot itself perturb the timings it is
/// copying.
const LAYER_STATS_MIRROR_INTERVAL: usize = 1_024;

/// A slot a *running* search copies its own [`NativeLayerStats`] into on a fixed
/// iteration cadence, so a thread that is not the search's can read partial
/// counters from a search that has not returned.
///
/// # Why anything published only on the way out is the wrong shape
///
/// Every instrument in this workspace publishes its snapshot when its stage
/// returns, into thread-local storage owned by the thread that ran the stage. A
/// harness that enforces a wall clock does it from a *different* thread (see
/// `axeyum-bench`'s `smtcomp_cli`): it gives up waiting, prints `unknown`, and
/// exits while the worker is still inside the search. Both halves of the
/// publish are then unreachable — the snapshot was never taken, and the thread
/// that would own it is not the thread asking. So the runs that most need
/// counters (the ones that time out) are exactly the runs that report none: 22
/// of 33 lost `QF_LRA` files printed no theory-layer line at all.
///
/// This is the missing half. The search stores a snapshot here every
/// `LAYER_STATS_MIRROR_INTERVAL` theory iterations, so a sampler on any
/// thread reads counters that are at most that many iterations stale.
///
/// # What a sample means, and what it does not
///
/// A sample is **partial by construction**: it is the state at some iteration
/// boundary, not at a verdict. `flushes` is what says so — it counts stores, so
/// a consumer can tell a mirrored mid-search sample from nothing at all, and
/// must never present a mirrored count as a completed total. Nothing here is
/// ever a rate's denominator.
///
/// # Cost
///
/// Off unless the caller both enables `Cdcl::collect_layer_stats` *and*
/// supplies a mirror; with either absent the added cost is one already-loaded
/// `bool` test per search-loop iteration and nothing else. With both, it is one
/// uncontended `Mutex` lock and a 15-field `Copy` store per 1,024 iterations —
/// deliberately not an atomic per counter increment, which would put a shared
/// write on the propagation path this instrument exists to time.
#[derive(Debug, Default)]
pub struct NativeLayerStatsMirror {
    /// The most recent snapshot, or `None` before the first flush.
    slot: Mutex<Option<NativeLayerStats>>,
    /// Completed stores. Monotone, and readable without taking the lock.
    flushes: AtomicU64,
}

impl NativeLayerStatsMirror {
    /// An empty mirror: no snapshot, no flushes.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Stores `stats`, overwriting whatever the previous flush left.
    ///
    /// A poisoned lock is recovered rather than propagated: this is telemetry,
    /// and a panic in one thread must not turn a diagnostic into a second
    /// panic in the search.
    fn store(&self, stats: NativeLayerStats) {
        let mut slot = self.slot.lock().unwrap_or_else(PoisonError::into_inner);
        *slot = Some(stats);
        drop(slot);
        self.flushes.fetch_add(1, Ordering::Relaxed);
    }

    /// The most recent snapshot and the number of flushes that produced it, or
    /// `None` when the search has not reached its first flush.
    ///
    /// Safe to call from any thread at any time, including while the search is
    /// running and including after it has been abandoned.
    #[must_use]
    pub fn sample(&self) -> Option<(NativeLayerStats, u64)> {
        let slot = self.slot.lock().unwrap_or_else(PoisonError::into_inner);
        (*slot).map(|stats| (stats, self.flushes.load(Ordering::Relaxed)))
    }
}

/// Search knobs a CDCL(T) caller may need to differ from the one-shot SAT
/// defaults (plan slice S7b).
///
/// The defaults ARE the one-shot SAT defaults, so
/// [`solve_with_theory_and_drat_proof`] is unchanged and so is every
/// `NullTheory` entry point. They exist because moving a route from
/// `axeyum_solver::cdclt::CdclT` onto this core has to be a swap of engines and
/// not, silently, a swap of decision heuristics: `CdclT` decides a variable
/// TRUE first and does no target rephasing, and a model-based consumer (MBQI
/// picks its instantiation terms out of the model it is handed) can lose a
/// verdict when the model changes even though both models are correct.
/// Measured: with the defaults below,
/// `auto::tests::mbqi_one_level_fixed_retry_is_guarded_and_replays_unfixed_seed_111_shape`
/// went `Sat` -> `Unknown` purely because a different satisfying assignment
/// came back.
// Three `bool` knobs plus a budget. They are named fields set individually by
// every caller, never positional arguments, so the confusion this lint guards
// against cannot arise; grouping them further would only add a level.
#[allow(clippy::struct_excessive_bools)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TheorySolveOptions {
    /// The polarity a variable is decided at before phase saving has an
    /// opinion. `false` is this core's own default (and `BatSat`'s);
    /// `CdclT` uses `true`.
    pub initial_phase: bool,
    /// Whether a restart rephases to the deepest conflict-free assignment seen
    /// (target rephasing). On for the one-shot SAT path; `CdclT` has no
    /// counterpart, so a route being moved off it turns this off.
    pub target_rephase: bool,
    /// Whether to accumulate [`NativeLayerStats`].
    pub collect_layer_stats: bool,
    /// Whether to record the Boolean DRAT stream, i.e. whether an `unsat`
    /// comes back with the ADR-1704 artifact at all.
    ///
    /// **Not free, and that is why it is a knob.** The stream is every learned
    /// clause of the whole search held in memory; on a 24-second CDCL(T) search
    /// with millions of conflicts that is gigabytes, and `CdclT` -- which emits
    /// no proof -- never paid it. A route that only needs the verdict (the
    /// dispatcher) turns this off and costs what it used to; the evidence layer,
    /// which is the only consumer of the artifact, turns it on.
    ///
    /// With it off, `unsat` comes back as
    /// [`TheorySolveOutcome::Unsat`]`(None)`. `None` means **not recorded** —
    /// never "no lemma was assumed", which is what
    /// `TheoryRefutation::theory_lemma_count() == 0` means and is a different
    /// statement entirely.
    pub record_proof: bool,
    /// How many DRAT literals the recording may hold before it is abandoned and
    /// the artifact reported ABSENT.
    ///
    /// Unbounded (`usize::MAX`) by default, which is what
    /// [`solve_with_theory_and_drat_proof`] has always been. A shipping route
    /// sets a finite one: a long CDCL(T) search learns millions of clauses, and
    /// holding all of them turned a front-door query that used to answer in
    /// seconds into one that did not answer at all. Overflow abandons the
    /// RECORDING, never the search -- the sink is output-only, so the verdict
    /// and the trajectory are the same either way, and the artifact's presence
    /// can never become part of what was decided.
    pub proof_literal_budget: usize,
}

impl Default for TheorySolveOptions {
    fn default() -> Self {
        Self {
            initial_phase: false,
            target_rephase: true,
            collect_layer_stats: false,
            record_proof: true,
            proof_literal_budget: usize::MAX,
        }
    }
}

/// Outcome of [`solve_with_theory_and_drat_proof`] -- the CDCL(T) counterpart
/// of [`ProofSolveOutcome`].
///
/// The one difference is `Unsat`: a refutation reached with a theory attached
/// is a [`TheoryRefutation`], not a bare `Vec<DratStep>`, because a DRAT stream
/// on its own does not say which formula it refutes and a CDCL(T) stream
/// refutes `cnf ++ lemmas` (ADR-1704). A run in which the theory contributed
/// nothing still comes back this way, with `theory_lemma_count() == 0`, so the
/// count is never absent and never zero-by-omission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TheoryProofOutcome {
    /// Satisfiable: a total assignment the Boolean side and the theory's
    /// `final_check` both accepted.
    Sat(CnfAssignment),
    /// Unsatisfiable modulo the enumerated theory lemmas, with the two-stream
    /// artifact ADR-1704 requires.
    Unsat(TheoryRefutation),
    /// The conflict budget was exhausted before a result was reached.
    ResourceOut,
    /// Undecided: the deadline passed, the theory step budget was exhausted, or
    /// the theory could not substantiate an answer it gave (an unresolvable
    /// explanation handle, an empty conflict core). Never a verdict.
    Interrupted,
}

/// Outcome of [`solve_with_theory_and_drat_proof_with_options`].
///
/// Differs from [`TheoryProofOutcome`] in exactly one respect: `Unsat` may come
/// back without an artifact, because the caller asked for a verdict only and
/// the search therefore recorded no DRAT stream. `None` there means **not
/// recorded**. It never means "no theory lemma was assumed" -- that is
/// `Some(artifact)` with `artifact.theory_lemma_count() == 0`, and a consumer
/// that conflated the two would report an unaudited refutation as an audited
/// one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TheorySolveOutcome {
    /// Satisfiable: a total assignment the Boolean side and the theory's
    /// `final_check` both accepted.
    Sat(CnfAssignment),
    /// Unsatisfiable modulo the theory, with the ADR-1704 artifact when the
    /// proof was recorded.
    Unsat(Option<TheoryRefutation>),
    /// The conflict budget was exhausted before a result was reached.
    ResourceOut,
    /// Undecided. Never a verdict.
    Interrupted,
}

/// Solves `formula` with `theory` attached, producing the ADR-1704 two-stream
/// artifact on `unsat`.
///
/// This is the CDCL(T) entry point: the same search, the same clause database,
/// the same 1-UIP analysis and the same DRAT emission as
/// [`solve_with_drat_proof_with_limits`], with the theory consulted at a
/// Boolean propagation fixpoint (`assert`, `propagate_into`, `take_new_atoms`)
/// and at a total assignment (`final_check`).
///
/// **`theory` is borrowed, not consumed**, so the caller reads its state back
/// afterwards to build a model -- the reason [`theory::NativeTheory`] is
/// implemented for `&mut T`.
///
/// # What `unsat` means here
///
/// Every clause that entered the database from the theory is in
/// [`TheoryRefutation::lemmas`] and in [`TheoryRefutation::extended`], and the
/// emitted stream is a DRAT proof of that extended formula -- **not** of
/// `formula`. Call [`TheoryRefutation::check`] to have `check_drat` say so.
/// With a lemma-free run the artifact is a plain propositional refutation and
/// checks `Verified`.
pub fn solve_with_theory_and_drat_proof<T: NativeTheory>(
    formula: &CnfFormula,
    theory: &mut T,
    deadline: Option<Instant>,
    max_conflicts: usize,
) -> TheoryProofOutcome {
    recorded_outcome(
        solve_with_theory_and_drat_proof_with_options(
            formula,
            theory,
            deadline,
            max_conflicts,
            TheorySolveOptions::default(),
        )
        .0,
    )
}

/// [`solve_with_theory_and_drat_proof`] with the search knobs spelled out.
///
/// Returns the outcome and the [`NativeLayerStats`] the run accumulated (all
/// zero unless `options.collect_layer_stats` is set -- an unmeasured run is
/// never a measured zero).
pub fn solve_with_theory_and_drat_proof_with_options<T: NativeTheory>(
    formula: &CnfFormula,
    theory: &mut T,
    deadline: Option<Instant>,
    max_conflicts: usize,
    options: TheorySolveOptions,
) -> (TheorySolveOutcome, NativeLayerStats) {
    solve_with_theory_and_drat_proof_impl(formula, theory, deadline, max_conflicts, options, None)
}

/// [`solve_with_theory_and_drat_proof_with_options`] with a
/// [`NativeLayerStatsMirror`] attached.
///
/// Identical in every observable way but one: while the search runs it copies
/// its own counters into `mirror` every `LAYER_STATS_MIRROR_INTERVAL` theory
/// iterations, so a thread that is not this one can read partial counters from
/// a search that has not returned — the case an external watchdog creates and
/// the case every on-the-way-out publish in this workspace misses. The returned
/// [`NativeLayerStats`] is unchanged and remains the complete, authoritative
/// figure; a mirrored sample is a mid-search reading and is never a substitute
/// for it.
///
/// `options.collect_layer_stats` still governs: with it clear nothing is
/// measured, so nothing is mirrored, and a caller that passes a mirror without
/// it gets an empty mirror rather than a run of measured zeros.
pub fn solve_with_theory_and_drat_proof_mirrored<T: NativeTheory>(
    formula: &CnfFormula,
    theory: &mut T,
    deadline: Option<Instant>,
    max_conflicts: usize,
    options: TheorySolveOptions,
    mirror: Option<Arc<NativeLayerStatsMirror>>,
) -> (TheorySolveOutcome, NativeLayerStats) {
    solve_with_theory_and_drat_proof_impl(formula, theory, deadline, max_conflicts, options, mirror)
}

/// Where a CDCL(T) search's DRAT steps go.
///
/// Two states rather than a generic parameter, for the same reason
/// `incremental::IncrementalSink` has two: the entry points above are one
/// concrete instantiation each, and recording is a run-time choice.
#[derive(Debug, Default)]
enum TheorySink {
    /// Steps are dropped. What a caller that wants only the verdict pays.
    #[default]
    Discard,
    /// Steps accumulate in memory, and an `unsat` can present the ADR-1704
    /// artifact -- unless the stream outgrows `remaining`, at which point the
    /// recording is abandoned and the artifact is reported ABSENT.
    Record {
        sink: VecProofSink,
        /// Literals still affordable. Counted in literals rather than steps
        /// because that is what the memory is: a 200-literal learned clause is
        /// two hundred times a unit.
        remaining: usize,
        /// Set once the budget is spent. From then on the sink accepts and
        /// drops, so the SEARCH is unaffected -- the sink is output-only, and a
        /// budget that changed the trajectory would make the artifact's
        /// presence part of the verdict.
        overflowed: bool,
    },
}

impl TheorySink {
    /// Charges `lits` against the budget, abandoning the recording (and
    /// releasing what it holds) when it does not fit.
    fn charge(&mut self, count: usize) -> bool {
        let TheorySink::Record {
            sink,
            remaining,
            overflowed,
        } = self
        else {
            return false;
        };
        if *overflowed {
            return false;
        }
        if count > *remaining {
            *overflowed = true;
            // Drop what was recorded: it is not going to be presented, and on
            // the searches this fires for it is the largest allocation alive.
            *sink = VecProofSink::new();
            return false;
        }
        *remaining -= count;
        true
    }
}

impl DratSink for TheorySink {
    fn add_clause(&mut self, lits: &[CnfLit]) -> Result<(), ProofSinkError> {
        if !self.charge(lits.len() + 1) {
            return Ok(());
        }
        match self {
            TheorySink::Discard => Ok(()),
            TheorySink::Record { sink, .. } => sink.add_clause(lits),
        }
    }

    fn delete_clause(&mut self, lits: &[CnfLit]) -> Result<(), ProofSinkError> {
        if !self.charge(lits.len() + 1) {
            return Ok(());
        }
        match self {
            TheorySink::Discard => Ok(()),
            TheorySink::Record { sink, .. } => sink.delete_clause(lits),
        }
    }
}

/// [`solve_with_theory_and_drat_proof`] with the driver-side instrument on.
///
/// Returns the same outcome plus the [`NativeLayerStats`] the search
/// accumulated. Collection costs a handful of `Instant::now()` pairs per
/// *stage boundary* (not per literal), so it is opt-in through this entry point
/// rather than switched on for every solve — the same discipline
/// `axeyum_solver::layers::TheoryLayerStats` follows on the `CdclT` side.
pub fn solve_with_theory_and_drat_proof_traced<T: NativeTheory>(
    formula: &CnfFormula,
    theory: &mut T,
    deadline: Option<Instant>,
    max_conflicts: usize,
) -> (TheoryProofOutcome, NativeLayerStats) {
    let (outcome, stats) = solve_with_theory_and_drat_proof_impl(
        formula,
        theory,
        deadline,
        max_conflicts,
        TheorySolveOptions {
            collect_layer_stats: true,
            ..TheorySolveOptions::default()
        },
        None,
    );
    (recorded_outcome(outcome), stats)
}

/// Narrows a [`TheorySolveOutcome`] produced with `record_proof` ON back to
/// [`TheoryProofOutcome`], whose `Unsat` always carries an artifact.
///
/// # Panics
///
/// Panics on an `Unsat` with no artifact, which means the caller passed
/// `record_proof: false` to an entry point that promises one. Unreachable from
/// the two callers, both of which set it.
fn recorded_outcome(outcome: TheorySolveOutcome) -> TheoryProofOutcome {
    match outcome {
        TheorySolveOutcome::Sat(model) => TheoryProofOutcome::Sat(model),
        TheorySolveOutcome::Unsat(Some(artifact)) => TheoryProofOutcome::Unsat(artifact),
        TheorySolveOutcome::Unsat(None) => {
            panic!("this entry point records the proof, so `unsat` carries an artifact")
        }
        TheorySolveOutcome::ResourceOut => TheoryProofOutcome::ResourceOut,
        TheorySolveOutcome::Interrupted => TheoryProofOutcome::Interrupted,
    }
}

fn solve_with_theory_and_drat_proof_impl<T: NativeTheory>(
    formula: &CnfFormula,
    theory: &mut T,
    deadline: Option<Instant>,
    max_conflicts: usize,
    options: TheorySolveOptions,
    mirror: Option<Arc<NativeLayerStatsMirror>>,
) -> (TheorySolveOutcome, NativeLayerStats) {
    let mut sink = if options.record_proof {
        TheorySink::Record {
            sink: VecProofSink::new(),
            remaining: options.proof_literal_budget,
            overflowed: false,
        }
    } else {
        TheorySink::Discard
    };
    let mut cdcl = Cdcl::new_with_theory(formula, &mut sink, theory);
    cdcl.collect_layer_stats = options.collect_layer_stats;
    cdcl.layer_stats_mirror = mirror;
    cdcl.use_target_rephase = options.target_rephase;
    if options.initial_phase {
        cdcl.initial_phase = true;
        cdcl.phase.fill(true);
        cdcl.best_phase.fill(true);
        cdcl.target_phase.fill(true);
    }
    let outcome = cdcl.run(&[], deadline, max_conflicts);
    let lemmas = core::mem::take(&mut cdcl.theory_lemmas);
    let stats = cdcl.native_layer_stats();
    drop(cdcl);
    (theory_proof_outcome(formula, lemmas, sink, outcome), stats)
}

fn theory_proof_outcome(
    formula: &CnfFormula,
    lemmas: Vec<Vec<CnfLit>>,
    sink: TheorySink,
    outcome: Result<SearchOutcome, ProofSinkError>,
) -> TheorySolveOutcome {
    match outcome {
        Ok(SearchOutcome::Sat(model)) => TheorySolveOutcome::Sat(model),
        Ok(SearchOutcome::Unsat) => TheorySolveOutcome::Unsat(match sink {
            TheorySink::Record {
                sink,
                overflowed: false,
                ..
            } => Some(TheoryRefutation::from_cnf_and_lemmas(
                formula.clone(),
                lemmas,
                sink.into_steps(),
            )),
            // Recording was off, or the stream outgrew its budget. `None` is
            // "not recorded", never "no lemma was assumed" -- that would be an
            // artifact with an empty lemma list, which is a different and much
            // stronger statement.
            TheorySink::Discard | TheorySink::Record { .. } => None,
        }),
        Ok(SearchOutcome::ResourceOut) => TheorySolveOutcome::ResourceOut,
        // `UnsatUnderAssumptions` is unreachable with no assumptions, and
        // `VecProofSink` is infallible so `Err` is too. Both fold into the
        // *undecided* outcome rather than panicking or guessing: an impossible
        // branch must never be able to produce a wrong `sat`/`unsat`.
        Ok(SearchOutcome::Interrupted | SearchOutcome::UnsatUnderAssumptions(_)) | Err(_) => {
            TheorySolveOutcome::Interrupted
        }
    }
}

/// The internal result of one CDCL search. Distinct from the public
/// [`StreamingProofOutcome`] in exactly one respect: it can report
/// *unsatisfiable under the given assumptions*, which is not a refutation of
/// the formula and therefore never emits an empty clause.
#[derive(Debug, Clone, PartialEq, Eq)]
enum SearchOutcome {
    /// Satisfiable; the model satisfies the clause database and every assumption.
    Sat(CnfAssignment),
    /// Unsatisfiable outright: the empty clause was derived and emitted.
    Unsat,
    /// Unsatisfiable under the assumptions that were passed. The payload is the
    /// subset of those assumptions sufficient for the contradiction (the
    /// final-conflict core). The clause database itself may well be satisfiable.
    UnsatUnderAssumptions(Vec<CnfLit>),
    /// The conflict budget was exhausted (undecided).
    ResourceOut,
    /// The wall-clock deadline passed (undecided).
    Interrupted,
}

fn lit_code(lit: CnfLit) -> usize {
    2 * lit.var().index() + usize::from(lit.is_negated())
}

/// One entry in a literal's watch list (the `MiniSat`/`BatSat` blocking-literal
/// scheme, plus Kissat's binary tag). `blocker` is a *cached* literal of the
/// watched clause OTHER than the watched one. In `propagate`, if `blocker` is
/// already true under the current assignment the clause is satisfied and is
/// skipped *without dereferencing the clause array* — the cache hit that makes
/// BCP fast. The blocker is purely a performance hint: it never changes which
/// propagations or conflicts are derived.
///
/// # The binary tag
///
/// `tagged` packs the clause reference with a one-bit `binary` flag in bit 0:
/// `cid << 1 | binary`. For a **binary** clause the blocker is not a hint but
/// the clause's *other literal in full* — a two-literal clause has exactly one
/// literal besides the watched one — so once the blocker's value is known the
/// propagation is decided:
///
/// * blocker true  → the clause is satisfied,
/// * blocker false → the clause is the conflict,
/// * blocker unassigned → the clause implies the blocker.
///
/// None of those three needs the clause header or the arena, so a binary watch
/// **never touches the clause arena at all** (Kissat `src/watch.h:18-42`,
/// `src/proplit.h:82-93`; `CaDiCaL`'s `Watch::binary` in `src/watch.hpp`). That
/// is the whole point of the tag: before it, every binary watch that missed the
/// blocker cache paid a header read, an arena read, a possible arena write and
/// an empty replacement scan to rediscover a literal the watch already held.
///
/// The tag is packed into the reference rather than added as a field because
/// [`WATCH_BYTES`] is a *model* constant that denominates every tick budget in
/// the tree: `CnfLit` is 8 bytes, so a `bool` field would push `Watch` from 16
/// to 24 bytes on a 64-bit target and silently re-denominate every budget. A
/// tag bit keeps the layout byte-identical, which the assertion below enforces.
///
/// # Invariant it gives up
///
/// A *long* clause keeps the classical placement: the two watched literals are
/// arena slots 0 and 1, and the implied literal of a propagation is slot 0. A
/// **binary** clause does not: nothing swaps its arena slots any more, so the
/// literal it implies may sit in either slot. Three readers used to assume
/// "slot 0 is the implied literal" and now identify that literal by *variable*
/// instead: [`Cdcl::is_locked`], [`Cdcl::lit_redundant`] and
/// [`Cdcl::analyze_final`]. `analyze` never assumed it (it skips the pivot by
/// variable already).
#[derive(Clone, Copy)]
struct Watch {
    /// `clause << 1 | u8::from(binary)`.
    tagged: usize,
    blocker: CnfLit,
}

impl Watch {
    /// A watch on a clause of length > 2: `blocker` is a cached hint.
    #[inline]
    fn long(clause: CRef, blocker: CnfLit) -> Self {
        Self::new(clause, blocker, false)
    }

    /// The tagged constructor. `binary` must be `len == 2`; every call site
    /// derives it from the clause it is watching rather than from a guess.
    #[inline]
    fn new(clause: CRef, blocker: CnfLit, binary: bool) -> Self {
        debug_assert!(
            clause <= usize::MAX >> 1,
            "clause reference does not fit beside the binary tag"
        );
        Self {
            tagged: (clause << 1) | usize::from(binary),
            blocker,
        }
    }

    /// The watched clause.
    #[inline]
    const fn clause(self) -> CRef {
        self.tagged >> 1
    }

    /// Whether the watched clause has exactly two literals, in which case
    /// [`Watch::blocker`] is the other one and no arena access is needed.
    #[inline]
    const fn is_binary(self) -> bool {
        self.tagged & 1 == 1
    }
}

/// Width of one [`Watch`], as the deterministic tick model
/// ([`crate::ticks`]) assumes it.
///
/// Pinned rather than computed so the tick unit cannot drift silently: budgets
/// are calibrated in ticks, and ticks are denominated in watches per assumed
/// cache line, so widening the watch re-denominates every budget in the tree.
/// The assertion below turns that into a build failure instead.
pub(crate) const WATCH_BYTES: usize = 16;

/// The width `Watch` actually has on THIS target.
///
/// Deliberately separate from [`WATCH_BYTES`], which is a **model** constant.
/// The two were the same number and got conflated, which broke the
/// `wasm32-unknown-unknown` build (a supported target, CLAUDE.md): `CRef` is a
/// `usize`, so `Watch` is 16 bytes on a 64-bit target and 12 on a 32-bit one,
/// and the pinned assertion below was only ever true for one pointer width.
///
/// They must NOT be unified in either direction:
///
/// * Deriving `WATCH_BYTES` from `size_of::<Watch>()` would make
///   `ticks::WATCHES_PER_CACHE_LINE` -- and therefore every budget denominated
///   in ticks -- differ between a 64-bit and a 32-bit host. Determinism is a
///   public API promise here, and it has to hold ACROSS platforms, not just
///   across runs on one. The tick is a model unit, not a measurement of the
///   machine it happens to be running on.
/// * Leaving the assertion pinned at 16 makes 32-bit targets unbuildable.
///
/// So: the model stays fixed at 16 everywhere, and the assertion checks the
/// real layout per target. Adding a field to `Watch` still breaks the build on
/// whichever target you compile, which is what the guard is for.
#[cfg(target_pointer_width = "64")]
const WATCH_BYTES_ON_TARGET: usize = 16;
#[cfg(target_pointer_width = "32")]
const WATCH_BYTES_ON_TARGET: usize = 12;

const _: () = assert!(
    size_of::<Watch>() == WATCH_BYTES_ON_TARGET,
    "`Watch` changed width: `ticks::WATCHES_PER_CACHE_LINE` and every budget \
     calibrated in ticks are denominated in it. Re-decide the constant \
     deliberately rather than letting the unit move."
);

/// What one [`Cdcl::theory_round`] concluded.
#[derive(Debug, Clone, PartialEq, Eq)]
enum TheoryRound {
    /// The theory added nothing: carry on to the restart check and the decision.
    Fixpoint,
    /// The theory enqueued at least one literal, or registered a new atom;
    /// re-run Boolean propagation before deciding anything else.
    Propagated,
    /// The theory refuted the current assignment. The payload is the conflict
    /// clause: every literal false under the current assignment (the
    /// convention in [`theory`]). The driver installs it as an ADR-1704 lemma
    /// and analyses it like any other conflict.
    Conflict(Vec<CnfLit>),
    /// The search must stop with this outcome (always *undecided*: a theory
    /// that cannot explain its own handle, or a conflict with an empty core).
    Stop(SearchOutcome),
}

/// A clause reference: a stable index into [`Cdcl::headers`] (and the parallel
/// per-clause metadata vectors). It is the identity used by watches, reasons,
/// and the proof — replacing the old `usize` clause id of the
/// `Vec<Vec<CnfLit>>` layout. [`CRef`]s never move: `headers` only grows
/// (learned clauses are appended) and deletion is by tombstone, so a [`CRef`]
/// stays valid
/// for the whole solve. The clause's literals live in the flat
/// [`Cdcl::arena`] at `[offset .. offset + len]`; that slice never relocates
/// either, since the arena only ever appends.
type CRef = usize;

/// The tag width of a [`Reason`]: the two high bits of the word.
const REASON_TAG_SHIFT: u32 = 62;
/// Payload mask: everything below the tag.
const REASON_PAYLOAD_MASK: u64 = (1u64 << REASON_TAG_SHIFT) - 1;
const REASON_TAG_DECISION: u64 = 0;
const REASON_TAG_CLAUSE: u64 = 1;
const REASON_TAG_THEORY: u64 = 2;

/// How an assigned variable came to be assigned -- its antecedent in the
/// implication graph (ADR-1701 slice-2 design memo section 4.4 (ii)).
///
/// Three cases, packed into **one word**:
///
/// - [`Reason::DECISION`] -- a decision literal, an installed assumption, or a
///   level-zero unit: no antecedent clause.
/// - `Clause(`[`CRef`]`)` -- the ordinary case: an arena clause whose slot 0 is
///   the implied literal and whose remaining literals are currently false.
/// - `Theory(`[`ExplanationId`]`)` -- a literal a [`NativeTheory`] implied with
///   a **lazy** explanation. The clause does not exist yet; the first time
///   conflict analysis, minimization or [`Cdcl::analyze_final`] needs it, the
///   handle is resolved through [`NativeTheory::explain`], the clause is
///   installed in the arena as an **input** clause (ADR-1704: a theory lemma
///   enters the Boolean stream as an extension of the input formula, never as
///   an unlabelled learned clause) and this reason is rewritten in place to
///   `Clause(cref)` -- so one handle is resolved at most once per assignment,
///   and the search never pays for an explanation it does not resolve against.
///   That saving is the entire point of the lazy channel.
///
/// # Why a packed word and not an enum
///
/// This is one entry per **variable**, read on every step of every conflict
/// analysis and on every step of recursive minimization. The representation it
/// replaces, `Option<CRef>`, is **16 bytes** on a 64-bit target (`usize` has no
/// niche, so the discriminant costs a whole extra word); the three-variant
/// `enum Reason { Decision, Clause(CRef), Theory(ExplanationId) }` is 16 bytes
/// for the same reason. This packing is **8 bytes**, so adding the theory case
/// *halves* per-variable reason memory rather than growing it. Pinned by
/// `tests::reason_is_one_word_and_no_wider_than_the_option_it_replaced`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Reason(u64);

/// The decoded form of a [`Reason`], for `match`ing. Never stored.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ReasonKind {
    Decision,
    Clause(CRef),
    Theory(ExplanationId),
}

impl Reason {
    /// No antecedent: a decision, an assumption, or a level-zero unit.
    const DECISION: Self = Self(REASON_TAG_DECISION << REASON_TAG_SHIFT);

    /// An arena clause antecedent.
    #[inline]
    fn clause(cref: CRef) -> Self {
        debug_assert!(
            (cref as u64) <= REASON_PAYLOAD_MASK,
            "clause reference exceeds the 62-bit Reason payload"
        );
        Self((REASON_TAG_CLAUSE << REASON_TAG_SHIFT) | (cref as u64))
    }

    /// A lazily-explained theory antecedent.
    ///
    /// # Panics
    ///
    /// Panics when `handle` does not fit the 62-bit payload. A silent truncation
    /// here would hand `explain` a different handle than the theory issued, so
    /// this is a hard error rather than a `debug_assert`.
    #[inline]
    fn theory(handle: ExplanationId) -> Self {
        assert!(
            handle.0 <= REASON_PAYLOAD_MASK,
            "explanation handle {} exceeds the 62-bit Reason payload",
            handle.0
        );
        Self((REASON_TAG_THEORY << REASON_TAG_SHIFT) | handle.0)
    }

    #[inline]
    fn tag(self) -> u64 {
        self.0 >> REASON_TAG_SHIFT
    }

    #[inline]
    fn payload(self) -> u64 {
        self.0 & REASON_PAYLOAD_MASK
    }

    /// Is this variable a decision (or assumption, or level-zero unit)?
    ///
    /// A single compare, not a shift-and-compare: `DECISION` is tag 0 with a
    /// zero payload, and every tagged case has a tag of at least
    /// [`REASON_TAG_CLAUSE`], so the whole word is below
    /// `REASON_TAG_CLAUSE << REASON_TAG_SHIFT` exactly for a decision. This is
    /// read once per literal in `lit_redundant`'s inner loop, which is why the
    /// instruction is worth naming.
    #[inline]
    fn is_decision(self) -> bool {
        debug_assert_eq!(REASON_TAG_DECISION, 0);
        self.0 < (REASON_TAG_CLAUSE << REASON_TAG_SHIFT)
    }

    /// The antecedent clause, when there already is one. `None` for a decision
    /// **and** for an unresolved theory reason -- callers that must have a
    /// clause go through [`Cdcl::resolve_reason`].
    // The payload of a CLAUSE reason is only ever written by `Reason::clause`
    // from a `CRef`, which IS a `usize`, so the round-trip cannot lose bits on
    // any pointer width -- including wasm32, where `usize` is 32 bits and this
    // lint is not hypothetical. A `try_from` here would put a fallible
    // conversion on the hottest read in conflict analysis to re-check an
    // invariant the constructor already holds; the `debug_assert` states it
    // instead.
    #[allow(clippy::cast_possible_truncation)]
    #[inline]
    fn as_clause(self) -> Option<CRef> {
        debug_assert!(self.tag() != REASON_TAG_CLAUSE || usize::try_from(self.payload()).is_ok());
        (self.tag() == REASON_TAG_CLAUSE).then(|| self.payload() as CRef)
    }

    /// The unresolved theory handle, if this is one.
    #[inline]
    fn as_theory(self) -> Option<ExplanationId> {
        (self.tag() == REASON_TAG_THEORY).then(|| ExplanationId(self.payload()))
    }

    /// Decoded, for `match`.
    // Same round-trip invariant as `as_clause`.
    #[allow(clippy::cast_possible_truncation)]
    #[inline]
    fn kind(self) -> ReasonKind {
        match self.tag() {
            REASON_TAG_DECISION => ReasonKind::Decision,
            REASON_TAG_CLAUSE => ReasonKind::Clause(self.payload() as CRef),
            _ => ReasonKind::Theory(ExplanationId(self.payload())),
        }
    }
}

impl core::fmt::Debug for Reason {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.kind() {
            ReasonKind::Decision => f.write_str("Decision"),
            ReasonKind::Clause(cref) => write!(f, "Clause({cref})"),
            ReasonKind::Theory(handle) => write!(f, "Theory({})", handle.0),
        }
    }
}

/// Per-clause index into the packed literal [`Cdcl::arena`]. Mirrors `BatSat`'s
/// `ClauseAllocator`/`ClauseHeader`: all clause literals are stored contiguously
/// in one cache-local arena, and each clause is described by its `(offset, len)`
/// here rather than by a separately-heap-allocated `Vec`. The two watched
/// literals are kept in arena slots `offset+0` and `offset+1` (the slot-0/1
/// convention), exactly as in the prior `Vec<CnfLit>` layout.
#[derive(Clone, Copy)]
struct ClauseHeader {
    offset: usize,
    len: usize,
}

/// The CDCL core, generic over where its proof goes (ADR-0381) and over the
/// theory attached to its search (ADR-1701 slice 2 spike; see
/// [`theory`]).
///
/// `S` is monomorphized, so the emission call at every learned clause and every
/// `reduce_db` deletion is a direct call — no `dyn` dispatch in the search loop.
/// The sink is *output only*: no field of this struct and no branch of the search
/// reads it back, which is why the trajectory is identical for every `S`.
///
/// `T` defaults to [`NullTheory`], which every shipping entry point uses: its
/// hooks are empty `#[inline(always)]` bodies and its
/// [`NativeTheory::HAS_THEORY`] is `false`, so a `Cdcl<'_, S, NullTheory>`
/// decides exactly what the pre-spike core decided, in the same order, with the
/// same DRAT stream.
// Four `bool` flags: three long-standing schedule/heuristic selectors
// (`has_empty_clause`, `use_target_rephase`, `use_ema_restart`) plus S7b's
// `collect_layer_stats`. Grouping them into a config struct would add an
// indirection to the search loop's reads to satisfy a lint about argument
// confusion at a positional CONSTRUCTOR this type does not have — every field
// is set by name in `new_with_theory`.
#[allow(clippy::struct_excessive_bools)]
struct Cdcl<'progress, S: DratSink, T: NativeTheory = NullTheory> {
    /// Where derived clauses and deletions are emitted, in derivation order.
    sink: S,
    /// Flat, cache-local arena of all clause literals (problem clauses first,
    /// learned clauses appended). A clause occupies the contiguous slice
    /// `arena[h.offset .. h.offset + h.len]` for its [`ClauseHeader`] `h`. The
    /// arena only grows; existing clause slices never move, so [`CRef`]s and the
    /// `(offset, len)` of already-registered clauses stay valid.
    arena: Vec<CnfLit>,
    /// Per-clause `(offset, len)` headers into [`Cdcl::arena`], indexed by
    /// [`CRef`]. `headers.len()` is the clause count.
    headers: Vec<ClauseHeader>,
    /// Per-literal watch lists, indexed by [`lit_code`]. Each entry carries a
    /// blocking literal (see [`Watch`]).
    watches: Vec<Vec<Watch>>,
    assign: Vec<Option<bool>>,
    level: Vec<usize>,
    reason: Vec<Reason>,
    trail: Vec<usize>,
    trail_lim: Vec<usize>,
    qhead: usize,
    initial_units: Vec<CnfLit>,
    /// `initial_unit_seen[v]` is set once variable `v` has contributed a literal
    /// to [`Cdcl::initial_units`]. Only the incremental path writes it (see
    /// [`Cdcl::reset_search_state`]); it keeps that path's de-duplication O(1)
    /// instead of a linear scan per level-zero literal.
    initial_unit_seen: Vec<bool>,
    has_empty_clause: bool,
    conflicts: usize,
    /// VSIDS activity per variable (higher ⇒ branched sooner).
    activity: Vec<f64>,
    /// Current activity bump increment (grows each conflict by `1/decay`).
    var_inc: f64,
    /// Saved decision polarity per variable (phase saving).
    phase: Vec<bool>,
    /// Variables occurring in at least one original clause.
    /// Variables absent from the formula need no decision and default false in
    /// a returned total assignment.
    branchable: Vec<bool>,
    /// Target-phase rephasing (T1.3.1): the decision polarities of the deepest
    /// (largest-trail) conflict-free assignment seen so far — the "closest to a
    /// model" phase. On a restart (when [`Cdcl::use_target_rephase`] is set) the
    /// saved [`Cdcl::phase`] is reset to this target, so search re-descends toward the
    /// best assignment instead of the last-seen polarities. Pure decision-order
    /// heuristic (verdict-preserving).
    best_phase: Vec<bool>,
    /// The trail length at which [`Cdcl::best_phase`] was last snapshotted.
    ///
    /// This is the **long-run archive** mark. It is deliberately monotone
    /// within a solve: `best_phase` is the deepest assignment the whole search
    /// ever reached, and a `Best` rephase restores from it. It is *not* what
    /// restarts read — see [`Cdcl::target_trail_len`] for why that distinction
    /// exists.
    best_trail_len: usize,
    /// Target phase: the polarities restarts re-descend into.
    ///
    /// Separate from [`Cdcl::best_phase`] because the two have opposite
    /// requirements. `best` must never release, or the archive is lost; `target`
    /// must release periodically, or the search is pinned.
    target_phase: Vec<bool>,
    /// The trail length at which [`Cdcl::target_phase`] was last snapshotted —
    /// a high-water mark that is **reset on every rephase**.
    ///
    /// Before 2026-09 there was one mark serving both roles and nothing ever
    /// reset it inside a solve. That is a ratchet with no release: once the
    /// search has had one deep dive, no later assignment beats the mark, the
    /// snapshot stops firing, and the restart-time `phase := best_phase` pins
    /// every subsequent descent into the same region for the rest of the run.
    /// Resetting the target mark is what makes the restart-time copy a
    /// *direction* rather than a commitment: the search is pushed to find larger
    /// and larger targets between rephases, and the largest is what lands in the
    /// archive.
    target_trail_len: usize,
    /// Phase installed by an `Original` rephase and used before any variable has
    /// been assigned. `false` unless the caller asked for an all-true initial
    /// phase.
    initial_phase: bool,
    /// Phase-policy state: the rephase schedule and its conflict interval.
    phase_policy: PhasePolicy,
    /// When set (the default), restarts rephase [`Cdcl::phase`] to
    /// [`Cdcl::best_phase`] (target rephasing); otherwise plain phase saving is kept.
    use_target_rephase: bool,
    /// Conflicts since the last restart (the restart trigger's interval counter).
    conflicts_since_restart: usize,
    /// Index into the Luby sequence (1-based; advances on each restart).
    restart_count: u64,
    /// Fast exponential moving average of learned-clause LBD (Glucose EMA restart).
    glue_fast: f64,
    /// Slow (long-run) exponential moving average of learned-clause LBD.
    glue_slow: f64,
    /// Slow exponential moving average of trail size at conflict — the reference
    /// for blocking restarts.
    trail_slow: f64,
    /// Restart schedule **currently in force** (T1.3.2). When set, the Glucose
    /// EMA glue rule drives restarts; otherwise the Luby schedule does.
    ///
    /// This is no longer a knob a caller sets. It is derived state, rewritten
    /// from [`Cdcl::restart_policy`] by [`Cdcl::sync_restart_schedule`] at
    /// construction, at [`Cdcl::set_policies`], and at every mode switch — so
    /// under [`SearchPolicies::mode_switching`] it flips back and forth within
    /// one solve, which is the whole point of the mode schedule.
    ///
    /// **Default is Luby (`false`).** The EMA rule is implemented, sound
    /// (verdict-preserving, DRAT-checked, deterministic) and measured on the public
    /// `p4dfa` `QF_BV` slice, where it came out **neutral-to-slightly-negative**: at
    /// both margins tried (`CaDiCaL` 1.10, `Glucose` 1.25) it improved `PAR-2` on the
    /// `MobileDevice` family (~18%) but lost one decide on `Composition`, and made no
    /// difference on the search-bound families (all timeout under either schedule).
    /// Combining it with rephasing and mode switching was the named next step;
    /// [`SearchPolicies::mode_switching`] is that combination, and it is
    /// selectable rather than default for the same measurement reason.
    use_ema_restart: bool,
    /// Whether the glue and trail moving averages are maintained.
    ///
    /// Distinct from [`Cdcl::use_ema_restart`], and deliberately so: under mode
    /// switching the averages must stay current *through* a stable phase, or
    /// re-entering focused mode would compare a fast average from before the
    /// gap against a slow one from after it. False under the default policy, so
    /// the default search executes no EMA arithmetic.
    track_restart_emas: bool,
    /// The stable/focused mode schedule. Under the default policy this never
    /// switches and every call into it is a `bool` test.
    restart_policy: RestartPolicy,
    /// Per-clause "this is a learned clause" flag, parallel to
    /// [`Cdcl::headers`]. Only learned clauses carry activity and only learned
    /// clauses are deletable by `reduce_db`.
    ///
    /// This replaced a single `num_original` boundary index. The boundary is
    /// correct only while every problem clause precedes every learned one,
    /// which the one-shot entry points guarantee but the incremental one does
    /// not: `add_clause` between solves appends a problem clause *after*
    /// learned clauses already exist, and under the old boundary that clause
    /// would have become a `reduce_db` deletion candidate — deleting an input
    /// clause weakens the formula and can produce a wrong `sat`. A per-clause
    /// flag cannot express that mistake. On the one-shot path the flag is
    /// exactly `cid >= num_original` was, so the search trajectory is
    /// unchanged.
    learned: Vec<bool>,
    /// Literal-block distance per clause (distinct decision levels among its
    /// literals). Written at learning time and lowered by promotion when the
    /// clause is resolved and its levels turn out to be more compact than they
    /// were. Meaningful for learned clauses only.
    lbd: Vec<usize>,
    /// Stamp table for [`Cdcl::compute_lbd`]: one generation tag per decision
    /// level. Paired with [`Cdcl::lbd_generation`] this counts distinct levels
    /// in O(clause length) with no allocation and no clearing pass.
    lbd_stamp: Vec<u64>,
    /// Monotone generation counter for [`Cdcl::lbd_stamp`]. A level counts as
    /// seen for the current clause iff its stamp equals this. `u64`, so it
    /// cannot wrap in any reachable run.
    lbd_generation: u64,
    /// Clause activity per clause (bumped when the clause participates in a
    /// conflict). Meaningful for learned clauses only.
    ///
    /// Maintained under every policy, but consulted by `reduce_db` only when
    /// [`ClauseDbPolicy::rank_key`] is `Activity`. The default tier policy
    /// ranks by `(glue desc, size desc)` and never reads this — as neither
    /// `CaDiCaL` nor Kissat does.
    cla_activity: Vec<f64>,
    /// Saturating lifetime counter per clause: set to
    /// [`crate::clause_db_policy::MAX_USED`] on learning and on every
    /// resolution through the clause, decremented once per `reduce_db` round.
    /// Meaningful for learned clauses only (a clause the policy can never
    /// delete never needs one).
    ///
    /// This is the signal the tier scheme is built on, and it differs from
    /// activity in the one way that matters: it *expires*. A clause resolved
    /// heavily long ago falls to zero and becomes deletable, where a decayed
    /// activity score merely becomes small and can still outrank a clause that
    /// was resolved last round.
    used: Vec<u8>,
    /// Tombstone flag: a deleted learned clause keeps its id (so reasons and
    /// later clause ids stay valid) but is removed from the watch lists and
    /// skipped everywhere. Original clauses are never tombstoned.
    deleted: Vec<bool>,
    /// Current clause-activity bump increment (grows each conflict).
    cla_inc: f64,
    /// Number of `reduce_db` reductions performed so far (drives the budget).
    reductions: usize,
    /// Clause-database policy: the keep predicate, the deletion ranking, the
    /// deleted fraction, and the dynamic tier boundaries (which are *state*, fed
    /// by every resolution). Swapping this object changes the whole reduce
    /// behaviour without touching the search loop; see
    /// [`ClauseDbPolicy::legacy`] for the pre-2026-09 baseline.
    db_policy: ClauseDbPolicy,
    /// Conflict count before which `reduce_db` will not attempt another round,
    /// set after a round that deleted nothing. Our reduce trigger is a
    /// learned-clause *budget*, not a conflict interval, so a database the keep
    /// rule fully protects would otherwise re-scan every clause on every
    /// conflict until the budget grew past it. The backoff bounds that to one
    /// scan per [`ClauseDbPolicy::empty_round_backoff`] conflicts and is
    /// counted in [`SearchCounters::reduce_empty_rounds`].
    reduce_backoff_until: u64,
    /// Conflict count at which the next `reduce_db` is due under the
    /// conflict-interval schedule. Unused (and zero) under the
    /// learned-clause-budget schedule, which reads the database size instead.
    /// See [`crate::clause_db_policy::ReduceSchedule`].
    next_reduce_conflicts: u64,
    /// Number of live (non-deleted) learned clauses. Drives the reduce trigger.
    learned_live: usize,
    /// Lowest clause id a reduce round still has to look at — Kissat's
    /// `first_reducible` (`reduce.c:37-61`).
    ///
    /// Everything below it is permanently uninteresting: a clause id's
    /// `learned` flag is written once at allocation and never changed, and
    /// `deleted` is monotone, so a prefix of ids that are all "input clause or
    /// already tombstoned" can never contain a future candidate. Advanced once
    /// per round by [`Cdcl::advance_reduce_scan_start`]; starts at 0, so the
    /// first round scans the whole database exactly as before and every later
    /// round skips at least the input clauses.
    reduce_scan_start: CRef,
    /// VSIDS order heap: a binary max-heap of variable indices keyed by
    /// `activity` (highest activity at the root), tie-broken by lowest index.
    /// `heap` holds the variables; `heap_pos[v]` is `v`'s position in `heap`,
    /// or [`HEAP_ABSENT`] when `v` is not in the heap. Lazy deletion: assigned
    /// variables are *not* removed on assignment — `pick_branch` pops the root
    /// and skips already-assigned variables, and `backtrack_to` re-inserts a
    /// variable only when it has been popped out (`heap_pos[v] == HEAP_ABSENT`).
    /// All operations are O(log n); the trajectory is identical to the prior
    /// O(n) linear scan because the ordering (`heap_before`) matches its
    /// highest-activity / lowest-index tie-break exactly.
    heap: Vec<usize>,
    heap_pos: Vec<usize>,
    /// Optional progress callback (see [`ProofSearchProgress`]), polled every
    /// [`Cdcl::progress_interval`] conflicts and once more at the end.
    /// `None` on every existing entry point — the observability hook is
    /// strictly opt-in via [`Cdcl::with_progress`].
    ///
    /// This is *output only*, exactly like [`Cdcl::sink`]: no branch of the
    /// search reads it back, so its presence, absence, or polling cadence
    /// cannot change the search trajectory (see
    /// `tests::progress_sink_does_not_change_the_verdict_or_proof`). Kept as a
    /// borrowed `dyn FnMut` (not a `Box`) so installing a sink allocates
    /// nothing here, and leaving it `None` costs one `Option` check per
    /// conflict on the hot path — no allocation, no syscall, no formatting.
    progress: Option<&'progress mut (dyn FnMut(&ProofSearchProgress) + Send)>,
    /// Conflict-count cadence for [`Cdcl::progress`] polls.
    progress_interval: usize,
    /// Total DRAT steps emitted so far. Only maintained while a progress sink
    /// is installed (see [`Cdcl::record_proof_step`]).
    proof_steps: usize,
    /// Total DRAT proof bytes (standard text format) emitted so far. Only
    /// maintained while a progress sink is installed.
    proof_bytes: u64,
    /// Wall-clock instant the search began, used only to compute
    /// [`ProofSearchProgress::elapsed`]. Cheap to record unconditionally (one
    /// clock read at construction, not on the hot path).
    search_start: Instant,
    /// The attached theory (ADR-1701 slice 2 spike). [`NullTheory`] on every
    /// shipping entry point.
    theory: T,
    /// Cursor into [`Cdcl::trail`] marking how far the theory has been told
    /// about assignments — the theory's own `qhead`, moved by
    /// [`Cdcl::theory_round`] and reset by [`Cdcl::backtrack_to`].
    theory_qhead: usize,
    /// The theory lemmas installed into the clause database so far, in
    /// installation order -- ADR-1704's `lemmas` stream.
    ///
    /// Every clause that entered the database from a theory rather than from
    /// 1-UIP resolution over input clauses is here, and each was registered as
    /// an **input** clause (`learned[cid] == false`), never as a learned one.
    /// So the Boolean stream this core emits is a DRAT proof of
    /// `cnf ++ theory_lemmas`, in that order, and the lemma count is the
    /// subtraction ADR-1704 section 1 requires --
    /// `theory_lemmas.len() == extended.len() - cnf.len()` -- rather than a
    /// number a producer asserts.
    ///
    /// Empty on every shipping entry point, all of which use [`NullTheory`]:
    /// a `NullTheory` never propagates, so no [`Reason::theory`] is ever
    /// created and nothing is ever installed here.
    theory_lemmas: Vec<Vec<CnfLit>>,
    /// The driver-owned propagation queue (ADR-1701). Owned for the whole
    /// search and cleared between fixpoint iterations, so its allocation is
    /// paid once instead of per `propagate` call.
    theory_queue: PropagationQueue,
    /// Search-loop iterations taken while a theory is attached, counted against
    /// [`THEORY_STEP_BUDGET`]. Never incremented for [`NullTheory`].
    theory_steps: usize,
    /// Whether this search accumulates [`NativeLayerStats`] (plan slice S7b
    /// step 1). `false` on every entry point but
    /// [`solve_with_theory_and_drat_proof_traced`]: when it is clear, no stage
    /// reads a clock and no counter is touched, so an unmeasured run is the
    /// search that existed before this field.
    collect_layer_stats: bool,
    /// Where this search copies its own [`NativeLayerStats`] every
    /// `LAYER_STATS_MIRROR_INTERVAL` theory iterations, so a thread other
    /// than this one can read partial counters from a search that never
    /// returns. `None` on every entry point that does not ask for one, which is
    /// all of them but `axeyum_solver`'s watchdog-instrumented route; see
    /// [`NativeLayerStatsMirror`] for why the on-the-way-out publish every
    /// other instrument uses is unreachable from a watchdog thread.
    ///
    /// Read together with `Cdcl::collect_layer_stats`: a mirror with
    /// collection off would flush all-zero snapshots, which is worse than no
    /// snapshot because it reads as a measured zero.
    layer_stats_mirror: Option<Arc<NativeLayerStatsMirror>>,
    time_boolean_propagate: Duration,
    time_theory_assert: Duration,
    time_theory_propagate: Duration,
    time_theory_push_pop: Duration,
    time_conflict_analysis: Duration,
    time_theory_final_check: Duration,
    time_theory_explain: Duration,
    stat_final_checks: u64,
    stat_theory_conflicts: u64,
    stat_theory_propagations: u64,
    stat_decisions: u64,
    stat_learned_clauses: u64,
    stat_learned_literals: u64,
    stat_learned_literals_premin: u64,
    /// Whether this search accumulates [`SearchCounters`]. `false` on every
    /// entry point but [`solve_with_drat_proof_counted`] and the progress-sink
    /// ones: when it is clear, no counter is touched, so an uncounted run is
    /// the search that existed before this field.
    ///
    /// Distinct from `Cdcl::collect_layer_stats` deliberately: that flag
    /// gates per-stage `Instant::now()` pairs, which are far more expensive
    /// than an integer increment and which perturb exactly the propagation
    /// timing a throughput measurement is trying to read.
    count_search: bool,
    /// The counters themselves; all zero unless [`Cdcl::count_search`] is set.
    counters: SearchCounters,
}

/// Sentinel in [`Cdcl::heap_pos`] marking a variable that is not currently in
/// the order heap (it has been popped by `pick_branch` and not yet re-inserted).
const HEAP_ABSENT: usize = usize::MAX;

impl<S: DratSink> Cdcl<'_, S, NullTheory> {
    /// The shipping constructor: the core with no theory attached.
    fn new(formula: &CnfFormula, sink: S) -> Self {
        Self::new_with_theory(formula, sink, NullTheory)
    }

    /// An empty solver: no variables, no clauses. The seed for the incremental
    /// entry point; [`Cdcl::ensure_vars`] and [`Cdcl::add_input_clause`] grow it
    /// between solves.
    fn new_empty(sink: S) -> Self {
        Self::new(&CnfFormula::new(0), sink)
    }
}

impl<'progress, S: DratSink, T: NativeTheory> Cdcl<'progress, S, T> {
    // One flat field-by-field initializer. Splitting it to satisfy a line count
    // would separate a field's default from the struct it belongs to for no
    // reader's benefit.
    #[allow(clippy::too_many_lines)]
    fn new_with_theory(formula: &CnfFormula, sink: S, theory: T) -> Self {
        let n = formula.variable_count();
        // Pack every clause's literals contiguously into one arena, recording a
        // `(offset, len)` header per clause. This mirrors the prior
        // `Vec<Vec<CnfLit>>` content exactly (same clauses, same order, same
        // intra-clause literal order) — only the storage layout differs.
        let mut arena: Vec<CnfLit> = Vec::new();
        let mut headers: Vec<ClauseHeader> = Vec::with_capacity(formula.clauses().len());
        for clause in formula.clauses() {
            let offset = arena.len();
            arena.extend_from_slice(clause.lits());
            headers.push(ClauseHeader {
                offset,
                len: clause.lits().len(),
            });
        }
        let mut watches = vec![Vec::new(); 2 * n];
        let mut initial_units = Vec::new();
        let mut has_empty_clause = false;
        for (cid, &h) in headers.iter().enumerate() {
            match h.len {
                0 => has_empty_clause = true,
                1 => initial_units.push(arena[h.offset]),
                _ => {
                    // Watch the first two literals; each watch's blocker is the
                    // OTHER watched literal of the same clause.
                    let (l0, l1) = (arena[h.offset], arena[h.offset + 1]);
                    let binary = h.len == 2;
                    watches[lit_code(l0)].push(Watch::new(cid, l1, binary));
                    watches[lit_code(l1)].push(Watch::new(cid, l0, binary));
                }
            }
        }
        let num_clauses = headers.len();
        let mut branchable = vec![false; n];
        for literal in &arena {
            branchable[literal.var().index()] = true;
        }
        // The shipped heuristics, taken from one place so the constructor cannot
        // drift from `SearchPolicies::default`.
        let policies = SearchPolicies::default();
        let mut cdcl = Self {
            sink,
            arena,
            headers,
            watches,
            assign: vec![None; n],
            level: vec![0; n],
            reason: vec![Reason::DECISION; n],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            initial_unit_seen: vec![false; n],
            initial_units,
            has_empty_clause,
            conflicts: 0,
            activity: vec![0.0; n],
            var_inc: 1.0,
            phase: vec![false; n],
            branchable,
            best_phase: vec![false; n],
            best_trail_len: 0,
            target_phase: vec![false; n],
            target_trail_len: 0,
            initial_phase: false,
            // The shipped defaults live in one place; see `SearchPolicies`.
            phase_policy: policies.phase,
            use_target_rephase: true,
            conflicts_since_restart: 0,
            restart_count: 1,
            glue_fast: 0.0,
            glue_slow: 0.0,
            trail_slow: 0.0,
            // Default is Luby: the EMA schedule is implemented and sound but measured
            // neutral-to-slightly-negative on the public p4dfa slice (see the field
            // doc), so it stays a selectable option, not the default. Both flags
            // below are derived from `restart_policy` and are re-synced by
            // `sync_restart_schedule` after this initializer runs, so they can
            // never disagree with the policy that owns them.
            use_ema_restart: false,
            track_restart_emas: false,
            restart_policy: policies.restart,
            learned: vec![false; num_clauses],
            lbd: vec![0; num_clauses],
            lbd_stamp: vec![0; n + 1],
            lbd_generation: 0,
            cla_activity: vec![0.0; num_clauses],
            used: vec![0; num_clauses],
            deleted: vec![false; num_clauses],
            cla_inc: 1.0,
            reductions: 0,
            db_policy: policies.clause_db,
            reduce_backoff_until: 0,
            next_reduce_conflicts: 0,
            learned_live: 0,
            reduce_scan_start: 0,
            heap: Vec::with_capacity(n),
            heap_pos: vec![HEAP_ABSENT; n],
            progress: None,
            progress_interval: DEFAULT_PROGRESS_CONFLICT_INTERVAL,
            proof_steps: 0,
            proof_bytes: 0,
            search_start: Instant::now(),
            theory,
            theory_qhead: 0,
            theory_lemmas: Vec::new(),
            theory_queue: PropagationQueue::new(),
            theory_steps: 0,
            collect_layer_stats: false,
            layer_stats_mirror: None,
            time_boolean_propagate: Duration::ZERO,
            time_theory_assert: Duration::ZERO,
            time_theory_propagate: Duration::ZERO,
            time_theory_push_pop: Duration::ZERO,
            time_conflict_analysis: Duration::ZERO,
            time_theory_final_check: Duration::ZERO,
            time_theory_explain: Duration::ZERO,
            stat_final_checks: 0,
            stat_theory_conflicts: 0,
            stat_theory_propagations: 0,
            stat_decisions: 0,
            stat_learned_clauses: 0,
            stat_learned_literals: 0,
            stat_learned_literals_premin: 0,
            count_search: false,
            counters: SearchCounters::default(),
        };
        // Seed the order heap with every variable that occurs in a clause.
        // Unused variables default false in a returned total model and must not
        // delay decisions on a sparse high-numbered projection. All activities are 0.0, so
        // the heap order is purely by index; inserting in ascending index order
        // builds a valid heap (each insert percolates up against equal-activity
        // parents whose index is smaller, so no swaps occur — O(n) total).
        for v in 0..n {
            if cdcl.branchable[v] {
                cdcl.heap_insert(v);
            }
        }
        cdcl.sync_restart_schedule();
        cdcl
    }

    /// Grows every per-variable table so variable indices `0 .. count` are legal.
    /// Idempotent and monotone; never shrinks.
    fn ensure_vars(&mut self, count: usize) {
        if count <= self.assign.len() {
            return;
        }
        self.assign.resize(count, None);
        self.level.resize(count, 0);
        self.reason.resize(count, Reason::DECISION);
        self.activity.resize(count, 0.0);
        self.phase.resize(count, false);
        self.best_phase.resize(count, false);
        self.target_phase.resize(count, self.initial_phase);
        self.lbd_stamp.resize(count + 1, 0);
        self.branchable.resize(count, false);
        self.heap_pos.resize(count, HEAP_ABSENT);
        self.initial_unit_seen.resize(count, false);
        self.watches.resize_with(2 * count, Vec::new);
    }

    /// Registers one **problem** clause into a solver that is between solves
    /// (nothing assigned, no decision levels). Returns the clause's [`CRef`], or
    /// `None` for a clause that was dropped as a tautology.
    ///
    /// Preconditions this relies on, all guaranteed by
    /// [`Cdcl::reset_search_state`] running before any `add_input_clause`: the
    /// trail is empty, so watching the first two literals is correct without any
    /// assignment-aware slot selection — exactly what [`Cdcl::new`] does for the
    /// initial formula.
    ///
    /// Literals are de-duplicated and tautologies (`x` together with `not x`)
    /// are dropped. Both are logic-preserving, and both matter here because a
    /// duplicated literal would otherwise put two watches on the same literal
    /// slot of one clause.
    fn add_input_clause(&mut self, lits: &[CnfLit]) -> Option<CRef> {
        debug_assert!(
            self.trail.is_empty(),
            "add_input_clause between solves only"
        );
        let mut normalized: Vec<CnfLit> = Vec::with_capacity(lits.len());
        for &lit in lits {
            if normalized.contains(&lit) {
                continue;
            }
            if normalized.contains(&lit.negated()) {
                return None; // tautology: satisfied by every assignment
            }
            normalized.push(lit);
        }
        let needed = normalized
            .iter()
            .map(|lit| lit.var().index() + 1)
            .max()
            .unwrap_or(0);
        self.ensure_vars(needed);

        let cid = self.alloc_clause(&normalized);
        self.lbd.push(0);
        self.cla_activity.push(0.0);
        // Not a learned clause: `reduce_db` can never delete it, so its
        // lifetime counter is never read. Pushed to keep the per-clause vectors
        // index-aligned.
        self.used.push(0);
        self.deleted.push(false);
        self.learned.push(false);

        match normalized.len() {
            0 => self.has_empty_clause = true,
            1 => self.initial_units.push(normalized[0]),
            _ => {
                let (l0, l1) = (normalized[0], normalized[1]);
                let binary = normalized.len() == 2;
                self.watches[lit_code(l0)].push(Watch::new(cid, l1, binary));
                self.watches[lit_code(l1)].push(Watch::new(cid, l0, binary));
            }
        }
        for lit in &normalized {
            let var = lit.var().index();
            if !self.branchable[var] {
                self.branchable[var] = true;
                if !self.heap_contains(var) {
                    self.heap_insert(var);
                }
            }
        }
        Some(cid)
    }

    /// Returns the solver to the "between solves" state: nothing assigned, no
    /// decision levels, every branchable variable back in the order heap, and
    /// the per-solve counters zeroed.
    ///
    /// What is deliberately **kept** is what makes this incremental: the clause
    /// database including every learned clause, VSIDS activities, saved phases,
    /// the target phase, and the clause-activity state. What is dropped is the
    /// level-0 trail — the accumulated units are re-propagated at the start of
    /// the next solve from [`Cdcl::initial_units`], which is cheap and removes
    /// every ordering subtlety around adding a clause that is already falsified.
    fn reset_search_state(&mut self) {
        // Promote every literal implied at decision level zero to a unit in
        // `initial_units`, so the next solve re-derives it by propagation
        // instead of by search. Level-zero literals are entailed by the clause
        // database alone, so this is sound; without it a *learned unit* clause
        // (which carries no watches and is not in `initial_units`) would be
        // silently lost at every solve boundary and the search would pay for it
        // again. Literals above level zero are excluded: they depend on
        // decisions, including assumptions, which do not survive the solve.
        let level_zero = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        for index in 0..level_zero {
            let var = self.trail[index];
            if self.initial_unit_seen[var] {
                continue;
            }
            self.initial_unit_seen[var] = true;
            let lit = self.true_literal(var);
            self.initial_units.push(lit);
        }
        for &var in &self.trail {
            self.assign[var] = None;
            self.reason[var] = Reason::DECISION;
        }
        // Unwind the theory in lockstep with the trail: one `pop` per level
        // this search pushed, and rewind its cursor. Level-zero assertions made
        // before the first `push` are NOT undone — the theory has no backtrack
        // point below level zero, exactly as `TheorySolver` defines it. That is
        // the right shape for a one-shot solve; a *warm* CDCL(T) across solves
        // needs a theory-side reset the trait does not have yet, and slice 2
        // proper has to decide whether that is a new trait method or a
        // fresh theory instance per solve (see the design memo).
        if T::HAS_THEORY {
            for _ in 0..self.trail_lim.len() {
                self.theory.pop();
            }
            self.theory_qhead = 0;
        }
        self.trail.clear();
        self.trail_lim.clear();
        self.qhead = 0;
        self.conflicts = 0;
        self.theory_steps = 0;
        self.conflicts_since_restart = 0;
        self.restart_count = 1;
        self.best_trail_len = 0;
        self.target_trail_len = 0;
        self.phase_policy.reset();
        self.restart_policy.reset();
        self.sync_restart_schedule();
        self.reduce_backoff_until = 0;
        self.next_reduce_conflicts = self.db_policy.next_reduce_limit(0, 0);
        for var in 0..self.branchable.len() {
            if self.branchable[var] && !self.heap_contains(var) {
                self.heap_insert(var);
            }
        }
    }

    /// Installs the clause-database and phase policies. Called before
    /// [`Cdcl::solve`]; the default entry points leave the defaults in place.
    fn set_policies(&mut self, policies: &SearchPolicies) {
        self.db_policy = policies.clause_db.clone();
        self.phase_policy = policies.phase.clone();
        self.restart_policy = policies.restart.clone();
        self.next_reduce_conflicts = self.db_policy.next_reduce_limit(0, 0);
        self.sync_restart_schedule();
        // The mode switch is denominated in ticks, and ticks are an exact
        // function of `SearchCounters`, so a policy that switches modes cannot
        // work with counting off — it would read zero ticks forever and never
        // leave its first phase. Enabling counting here rather than requiring
        // the caller to remember is the only arrangement in which the feature
        // cannot be silently inert, which is the failure mode this whole item
        // exists to remove.
        if self.restart_policy.needs_ticks() {
            self.count_search = true;
        }
    }

    /// Rewrites the derived restart flags from [`Cdcl::restart_policy`].
    ///
    /// Called at construction, when policies are installed, and after every
    /// mode switch. The flags exist so the hot paths (`should_restart`, the
    /// per-conflict EMA update) read one `bool` instead of matching on a mode.
    fn sync_restart_schedule(&mut self) {
        self.use_ema_restart = self.restart_policy.schedule() == RestartSchedule::Ema;
        self.track_restart_emas = self.restart_policy.tracks_emas();
    }

    /// Considers a mode switch. Called once per analysed conflict, which is
    /// where the reference calls `stabilizing()` from too (`restarting()`, once
    /// per restart check, itself gated on the conflict count).
    ///
    /// Returns early on one `bool` test unless mode switching is enabled, so
    /// the default search pays nothing — in particular it never evaluates the
    /// tick total.
    fn consider_mode_switch(&mut self) {
        if !self.restart_policy.needs_ticks() {
            return;
        }
        let conflicts = self.conflicts as u64;
        let ticks = self.counters.ticks();
        if !self.restart_policy.should_switch(conflicts, ticks) {
            return;
        }
        self.restart_policy.switch(conflicts, ticks);
        self.sync_restart_schedule();
        self.counters.mode_switches += 1;
        // A mode change replaces the restart rule, so the interval counter the
        // outgoing rule was accumulating means nothing to the incoming one:
        // carrying it over would make the first Luby phase after a long focused
        // phase fire immediately. The reluctant-doubling INDEX is deliberately
        // not reset — the reference keeps one persistent reluctant sequence
        // across the whole solve rather than restarting it per phase.
        self.conflicts_since_restart = 0;
    }

    /// What the mode schedule did, at the current tick total. Zero-valued and
    /// focused under every policy that does not switch.
    fn mode_schedule(&self) -> ModeSchedule {
        self.restart_policy.snapshot(self.counters.ticks())
    }

    /// Installs a progress callback, polled every `interval` conflicts (and
    /// once more when the search ends) with a cumulative
    /// [`ProofSearchProgress`] snapshot. `interval` is clamped to at least 1.
    ///
    /// Builder-style, called before [`Cdcl::solve`]; every existing entry
    /// point never calls this, so `progress` stays `None` and the hot-path
    /// cost stays a single `Option::is_none` check (see the field doc).
    fn with_progress(
        mut self,
        interval: usize,
        progress: &'progress mut (dyn FnMut(&ProofSearchProgress) + Send),
    ) -> Self {
        self.progress = Some(progress);
        self.progress_interval = interval.max(1);
        self
    }

    /// Records one emitted DRAT step (`add` when `delete` is `false`) toward
    /// [`Cdcl::proof_steps`] / [`Cdcl::proof_bytes`] — but ONLY when a progress
    /// sink is installed. The `is_none` check is the first thing this function
    /// does, so with no sink installed a call here costs one predictable
    /// branch and nothing else: no digit-counting loop, no counter writes.
    #[inline]
    fn record_proof_step(&mut self, delete: bool, lits: &[CnfLit]) {
        if self.progress.is_none() {
            return;
        }
        self.proof_steps += 1;
        self.proof_bytes += step_text_bytes(delete, lits);
    }

    /// Builds and delivers a [`ProofSearchProgress`] snapshot to the installed
    /// sink, if any. Called unconditionally at the natural reporting points
    /// ([`Cdcl::maybe_report_progress`] gates the per-conflict cadence; the
    /// terminal call in [`Cdcl::run`] always fires once more so the final
    /// numbers are never stale by up to `progress_interval` conflicts).
    fn report_progress(&mut self) {
        let Some(sink) = self.progress.as_mut() else {
            return;
        };
        let snapshot = ProofSearchProgress {
            conflicts: self.conflicts,
            learned_clauses: self.learned_live,
            proof_steps: self.proof_steps,
            proof_bytes: self.proof_bytes,
            elapsed: self.search_start.elapsed(),
        };
        sink(&snapshot);
    }

    /// Polls the progress sink on the conflict-count cadence
    /// ([`Cdcl::progress_interval`]). A no-op — one `is_none` check, nothing
    /// more — whenever no sink is installed.
    #[inline]
    fn maybe_report_progress(&mut self) {
        if self.progress.is_none() {
            return;
        }
        if self.conflicts.is_multiple_of(self.progress_interval) {
            self.report_progress();
        }
    }

    /// The literals of clause `cid`, as a cache-local slice into the arena.
    #[inline]
    fn lits(&self, cid: CRef) -> &[CnfLit] {
        let h = self.headers[cid];
        &self.arena[h.offset..h.offset + h.len]
    }

    /// The number of literals in clause `cid`.
    #[inline]
    fn clause_len(&self, cid: CRef) -> usize {
        self.headers[cid].len
    }

    /// The `i`-th literal of clause `cid` (0-based within the clause).
    #[inline]
    fn lit_at(&self, cid: CRef, i: usize) -> CnfLit {
        let h = self.headers[cid];
        self.arena[h.offset + i]
    }

    /// Appends a clause's literals to the arena and pushes its header, returning
    /// the new clause's stable [`CRef`]. The arena only grows here, so no
    /// existing clause slice moves.
    fn alloc_clause(&mut self, lits: &[CnfLit]) -> CRef {
        let offset = self.arena.len();
        self.arena.extend_from_slice(lits);
        let cid = self.headers.len();
        self.headers.push(ClauseHeader {
            offset,
            len: lits.len(),
        });
        cid
    }

    /// Order-heap comparator: returns `true` when variable `a` should sit closer
    /// to the root than `b`, i.e. `a` is the *preferred* branching variable.
    /// Highest activity wins; ties break to the lower index. This mirrors the
    /// prior linear scan exactly, keeping the search trajectory identical.
    fn heap_before(&self, a: usize, b: usize) -> bool {
        let (aa, ab) = (self.activity[a], self.activity[b]);
        // Exact `f64` equality is intentional and load-bearing: it must detect
        // ties *exactly* the way the reference linear scan does (which replaces
        // the best only on a strictly-greater activity, i.e. keeps the lower
        // index on bitwise-equal activity). An epsilon would change the
        // tie-break and so the search trajectory. The two activities are produced
        // by identical arithmetic, so bitwise equality is the correct predicate.
        #[allow(clippy::float_cmp)]
        let tie = aa == ab;
        aa > ab || (tie && a < b)
    }

    /// Restores the heap property by moving the element at `i` toward the root
    /// while it precedes its parent. O(log n).
    fn heap_percolate_up(&mut self, mut i: usize) {
        let x = self.heap[i];
        while i != 0 {
            let parent = (i - 1) / 2;
            let p = self.heap[parent];
            if !self.heap_before(x, p) {
                break;
            }
            self.heap[i] = p;
            self.heap_pos[p] = i;
            i = parent;
        }
        self.heap[i] = x;
        self.heap_pos[x] = i;
    }

    /// Restores the heap property by moving the element at `i` toward the leaves
    /// while a child precedes it. O(log n).
    fn heap_percolate_down(&mut self, mut i: usize) {
        let x = self.heap[i];
        let len = self.heap.len();
        loop {
            let left = 2 * i + 1;
            if left >= len {
                break;
            }
            let right = left + 1;
            let child = if right < len && self.heap_before(self.heap[right], self.heap[left]) {
                right
            } else {
                left
            };
            let c = self.heap[child];
            if !self.heap_before(c, x) {
                break;
            }
            self.heap[i] = c;
            self.heap_pos[c] = i;
            i = child;
        }
        self.heap[i] = x;
        self.heap_pos[x] = i;
    }

    /// True when `var` currently lives in the order heap.
    fn heap_contains(&self, var: usize) -> bool {
        self.heap_pos[var] != HEAP_ABSENT
    }

    /// Inserts `var` into the order heap (no-op if already present). O(log n).
    fn heap_insert(&mut self, var: usize) {
        if self.heap_contains(var) {
            return;
        }
        let i = self.heap.len();
        self.heap.push(var);
        self.heap_pos[var] = i;
        self.heap_percolate_up(i);
    }

    /// Removes and returns the root (preferred) variable. O(log n). The caller
    /// must ensure the heap is non-empty.
    fn heap_remove_min(&mut self) -> usize {
        let root = self.heap[0];
        let last = *self.heap.last().expect("heap not empty");
        self.heap_pos[root] = HEAP_ABSENT;
        if self.heap.len() == 1 {
            self.heap.pop();
            return root;
        }
        self.heap[0] = last;
        self.heap_pos[last] = 0;
        self.heap.pop();
        self.heap_percolate_down(0);
        root
    }

    /// Bumps `var`'s VSIDS activity, rescaling all activities if it overflows the
    /// cap (preserving their relative order).
    fn bump_var(&mut self, var: usize) {
        self.activity[var] += self.var_inc;
        if self.activity[var] > VSIDS_RESCALE_LIMIT {
            // Rescale every activity (and `var_inc`) by the same positive factor.
            // This preserves the *strict* order of distinct activities, BUT it can
            // collapse two distinct tiny activities to an equal value (rounding /
            // underflow to 0.0). Our comparator's secondary key is the variable
            // index, so a newly-formed tie introduces an ordering constraint the
            // existing heap layout never enforced — silently violating the heap
            // property. Re-heapify from scratch so the heap matches the post-
            // rescale total order exactly. Rescale is rare (activity must exceed
            // 1e100), so this O(n) rebuild does not affect amortized per-decision
            // cost; every other heap operation stays O(log n).
            for a in &mut self.activity {
                *a *= VSIDS_RESCALE;
            }
            self.var_inc *= VSIDS_RESCALE;
            self.heap_rebuild();
            return;
        }
        // The variable's activity only ever *increases* here, so it can only move
        // toward the root: a single sift-up restores the heap. O(log n). Variables
        // not currently in the heap (assigned-and-popped) need no update — they
        // are re-inserted at their (now higher) activity when they unassign.
        if self.heap_contains(var) {
            let i = self.heap_pos[var];
            self.heap_percolate_up(i);
        }
    }

    /// Rebuilds the order heap in place over its current membership, restoring
    /// the heap property under the current `activity` values (and the index
    /// tie-break). Floyd's bottom-up heapify: O(n) over the heap's size. Used
    /// after a VSIDS rescale, which can collapse distinct activities into ties
    /// and thereby invalidate the prior layout.
    fn heap_rebuild(&mut self) {
        let len = self.heap.len();
        if len <= 1 {
            return;
        }
        // Percolate down every internal node, highest index first (Floyd build).
        let mut i = len / 2;
        loop {
            i -= 1;
            self.heap_percolate_down(i);
            if i == 0 {
                break;
            }
        }
    }

    /// Decays activity by growing the bump increment (the `MiniSat` trick).
    fn decay(&mut self) {
        self.var_inc /= VSIDS_DECAY;
    }

    /// Conflicts allowed before the next restart, per the Luby schedule.
    fn restart_limit(&self) -> usize {
        usize::try_from(luby(self.restart_count)).unwrap_or(usize::MAX) * LUBY_UNIT
    }

    /// Update the Glucose EMA restart state from a just-analyzed conflict: the
    /// fast/slow LBD (glue) averages and the slow trail average (blocking
    /// reference), sampled at the conflict trail. Pure `f64` arithmetic in a fixed
    /// order, so the restart schedule stays fully deterministic.
    ///
    /// The `usize -> f64` casts are exact: an LBD and a trail length are both bounded
    /// by the variable count, far below `f64`'s 2^53 integer-exact range.
    #[allow(clippy::cast_precision_loss)]
    fn update_restart_emas(&mut self, lbd: usize) {
        let glue = lbd as f64;
        self.glue_fast += GLUE_EMA_FAST_ALPHA * (glue - self.glue_fast);
        self.glue_slow += GLUE_EMA_SLOW_ALPHA * (glue - self.glue_slow);
        let trail = self.trail.len() as f64;
        self.trail_slow += TRAIL_EMA_ALPHA * (trail - self.trail_slow);
    }

    /// Whether to restart now.
    ///
    /// EMA (Glucose) mode — the default: after a conflict warmup and a minimum
    /// inter-restart interval, restart when the fast glue average exceeds the slow
    /// one by [`RESTART_MARGIN`] (recent learned clauses are less reusable, so the
    /// current decision prefix is unproductive), **unless** a blocking condition
    /// holds — the trail is more than [`BLOCKING_MARGIN`]× its slow average, i.e.
    /// the search is deep and likely near a model, so a restart would waste it.
    ///
    /// Luby mode — the retained fallback: the legacy reluctant-doubling schedule.
    ///
    /// The `trail.len() as f64` cast is exact (trail length ≤ variable count ≪ 2^53).
    #[allow(clippy::cast_precision_loss)]
    fn should_restart(&self) -> bool {
        if !self.use_ema_restart {
            return self.conflicts_since_restart >= self.restart_limit();
        }
        if self.conflicts < EMA_RESTART_WARMUP
            || self.conflicts_since_restart < MIN_RESTART_INTERVAL
        {
            return false;
        }
        // Blocking restart: don't abandon a deep trail (near-model) prefix.
        if self.trail_slow > 0.0 && (self.trail.len() as f64) > BLOCKING_MARGIN * self.trail_slow {
            return false;
        }
        self.glue_fast > RESTART_MARGIN * self.glue_slow
    }

    /// Snapshot the current conflict-free assignment as the target phase when it is
    /// the deepest (largest-trail) one seen so far — the polarities "closest to a
    /// model" (T1.3.1). Reads `assign` directly (a disjoint field from `best_phase`),
    /// and only walks the trail on a fresh high-water mark, so the amortized cost is
    /// negligible.
    fn snapshot_target_phase(&mut self) {
        let depth = self.trail.len();
        let fresh_target = depth > self.target_trail_len;
        let fresh_best = depth > self.best_trail_len;
        if !fresh_target && !fresh_best {
            return;
        }
        if fresh_target {
            self.target_trail_len = depth;
            if self.count_search {
                self.counters.target_phase_snapshots += 1;
            }
        }
        if fresh_best {
            self.best_trail_len = depth;
            if self.count_search {
                self.counters.best_phase_snapshots += 1;
            }
        }
        for idx in 0..depth {
            let var = self.trail[idx];
            let polarity = self.assign[var] == Some(true);
            if fresh_target {
                self.target_phase[var] = polarity;
            }
            if fresh_best {
                self.best_phase[var] = polarity;
            }
        }
    }

    /// Applies one scheduled rephase: installs a phase vector and releases the
    /// target high-water mark so the ratchet can move again.
    ///
    /// Called at a restart, where the trail is about to be (or has just been)
    /// unwound to level 0, so overwriting the saved phases cannot contradict a
    /// live assignment.
    fn apply_rephase(&mut self, action: RephaseAction) {
        if self.count_search {
            self.counters.rephases += 1;
            self.counters.target_phase_resets += 1;
        }
        match action {
            // Release the mark and change nothing else: the search keeps its
            // saved phases and simply regains the ability to record a target.
            RephaseAction::TargetOnly => {}
            RephaseAction::Best => {
                self.phase.copy_from_slice(&self.best_phase);
                // The archive has been consumed; let it be rebuilt from the
                // targets found between now and the next `Best`.
                self.best_trail_len = 0;
            }
            RephaseAction::Inverted => {
                self.phase.fill(!self.initial_phase);
            }
            RephaseAction::Original => {
                self.phase.fill(self.initial_phase);
            }
        }
        // The target restarts read is re-seeded from the saved phases and its
        // mark released, so the next deep dive -- however shallow relative to
        // the run's best -- becomes the new target.
        self.target_phase.copy_from_slice(&self.phase);
        self.target_trail_len = 0;
    }

    fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    fn value(&self, lit: CnfLit) -> Option<bool> {
        self.assign[lit.var().index()].map(|v| v != lit.is_negated())
    }

    fn true_literal(&self, var: usize) -> CnfLit {
        let positive = CnfLit::positive(CnfVar::new(var).expect("variable index in range"));
        if self.assign[var] == Some(true) {
            positive
        } else {
            positive.negated()
        }
    }

    fn enqueue(&mut self, lit: CnfLit, reason: Reason) {
        let var = lit.var().index();
        let value = !lit.is_negated();
        self.assign[var] = Some(value);
        self.phase[var] = value; // phase saving: remember the last polarity
        self.level[var] = self.decision_level();
        self.reason[var] = reason;
        self.trail.push(var);
    }

    /// Runs the search, mapping a sink failure to
    /// [`StreamingProofOutcome::SinkFailed`]. Splitting the fallible body out
    /// keeps every emission site a plain `?` instead of a hand-written early
    /// return, so no proof step can be silently dropped on the error path.
    /// Lifts this search's accumulated stage timings and counters into
    /// [`NativeLayerStats`] — the native-core counterpart of
    /// `CdclT::theory_layer_stats`.
    ///
    /// All-zero when `Cdcl::collect_layer_stats` was never set, which is the
    /// honest reading: nothing was measured. `restarts` is derived from
    /// `restart_count`, which starts at 1 and advances once per completed
    /// restart — the same `restart_index - 1` `CdclT::restarts` computes.
    fn native_layer_stats(&self) -> NativeLayerStats {
        NativeLayerStats {
            boolean_propagate: self.time_boolean_propagate,
            theory_assert: self.time_theory_assert,
            theory_propagate: self.time_theory_propagate,
            theory_push_pop: self.time_theory_push_pop,
            conflict_analysis: self.time_conflict_analysis,
            theory_final_check: self.time_theory_final_check,
            theory_explain: self.time_theory_explain,
            final_checks: self.stat_final_checks,
            theory_conflicts: self.stat_theory_conflicts,
            theory_propagations: self.stat_theory_propagations,
            decisions: self.stat_decisions,
            learned_clauses: self.stat_learned_clauses,
            learned_literals: self.stat_learned_literals,
            learned_literals_before_minimization: self.stat_learned_literals_premin,
            restarts: if self.collect_layer_stats {
                self.restart_count - 1
            } else {
                0
            },
        }
    }

    /// [`Cdcl::solve`], additionally returning the [`SearchCounters`] this
    /// search accumulated. Counting is switched on here and nowhere else on the
    /// one-shot path.
    fn solve_counted(
        self,
        deadline: Option<Instant>,
        max_conflicts: usize,
    ) -> (StreamingProofOutcome, SearchCounters) {
        let (outcome, counters, _modes) = self.solve_counted_traced(deadline, max_conflicts);
        (outcome, counters)
    }

    /// [`Cdcl::solve_counted`], additionally returning the stable/focused mode
    /// schedule the search followed.
    fn solve_counted_traced(
        mut self,
        deadline: Option<Instant>,
        max_conflicts: usize,
    ) -> (StreamingProofOutcome, SearchCounters, ModeSchedule) {
        self.count_search = true;
        let outcome = self.solve_inner(deadline, max_conflicts);
        let modes = self.mode_schedule();
        (outcome, self.counters, modes)
    }

    fn solve(mut self, deadline: Option<Instant>, max_conflicts: usize) -> StreamingProofOutcome {
        self.solve_inner(deadline, max_conflicts)
    }

    fn solve_inner(
        &mut self,
        deadline: Option<Instant>,
        max_conflicts: usize,
    ) -> StreamingProofOutcome {
        match self.run(&[], deadline, max_conflicts) {
            Ok(SearchOutcome::Sat(model)) => StreamingProofOutcome::Sat(model),
            Ok(SearchOutcome::Unsat) => StreamingProofOutcome::Unsat,
            Ok(SearchOutcome::ResourceOut) => StreamingProofOutcome::ResourceOut,
            // `UnsatUnderAssumptions` is unreachable with no assumptions: its
            // only producer is the assumption-install branch, which
            // `assumptions.is_empty()` never enters. It is folded in with
            // `Interrupted` -- the *undecided* verdict -- rather than panicking
            // or guessing, so an impossible branch can never become a wrong
            // `sat`/`unsat`.
            Ok(SearchOutcome::Interrupted | SearchOutcome::UnsatUnderAssumptions(_)) => {
                StreamingProofOutcome::Interrupted
            }
            Err(error) => StreamingProofOutcome::SinkFailed(error),
        }
    }

    /// Propagates the accumulated units at level 0 and runs the search under
    /// `assumptions` (empty on every one-shot entry point).
    fn run(
        &mut self,
        assumptions: &[CnfLit],
        deadline: Option<Instant>,
        max_conflicts: usize,
    ) -> Result<SearchOutcome, ProofSinkError> {
        // A budget of zero conflicts admits no search at all, not even the
        // level-zero propagation below. `resource_limit = 0` means "encode but
        // do not solve" across this tree -- `SatBvBackend`'s CNF-shape
        // diagnostics rely on it, and so does the warm engine's per-check
        // budget test. Without this guard a formula that needs no conflict
        // (most easy instances) would be decided in spite of the budget, which
        // is not wrong but is not what the caller asked for.
        if max_conflicts == 0 {
            self.report_progress();
            return Ok(SearchOutcome::ResourceOut);
        }
        if self.has_empty_clause {
            self.record_proof_step(false, &[]);
            self.sink.add_clause(&[])?;
            self.report_progress();
            return Ok(SearchOutcome::Unsat);
        }
        // Indexed rather than drained: the incremental core re-propagates the
        // same units at the start of every solve, so `initial_units` must
        // survive this loop. On the one-shot path draining and reading are
        // indistinguishable.
        let mut index = 0;
        while index < self.initial_units.len() {
            let lit = self.initial_units[index];
            index += 1;
            match self.value(lit) {
                Some(false) => {
                    self.record_proof_step(false, &[]);
                    self.sink.add_clause(&[])?;
                    self.report_progress();
                    return Ok(SearchOutcome::Unsat);
                }
                Some(true) => {}
                None => self.enqueue(lit, Reason::DECISION),
            }
        }
        self.search_loop(assumptions, deadline, max_conflicts)
    }

    /// The main CDCL loop: propagate, learn from a conflict (or restart/decide
    /// when there is none), until the formula is decided or a budget is
    /// exhausted. Split out of [`Cdcl::run`] purely to keep both under
    /// clippy's line-count lint; behaviour is exactly the tail of `run` this
    /// replaced.
    // The loop is one decision procedure and reads as one; splitting the
    // conflict half from the decision half to satisfy a line count would put
    // the trail/level invariants they share across a function boundary.
    #[allow(clippy::too_many_lines)]
    fn search_loop(
        &mut self,
        assumptions: &[CnfLit],
        deadline: Option<Instant>,
        max_conflicts: usize,
    ) -> Result<SearchOutcome, ProofSinkError> {
        loop {
            // Theory-only termination guard (see `THEORY_STEP_BUDGET`) and the
            // theory-only clock. Both are behind `HAS_THEORY`, so for
            // `NullTheory` the whole block is dropped at monomorphization and
            // the shipping SAT trajectory -- including which conflict the clock
            // is read on -- is byte-identical to before.
            if T::HAS_THEORY {
                self.theory_steps += 1;
                if self.theory_steps > THEORY_STEP_BUDGET {
                    self.report_progress();
                    return Ok(SearchOutcome::Interrupted);
                }
                // The Boolean core reads the clock on a conflict cadence, which
                // a theory that propagates without ever conflicting never
                // reaches. Read it on an iteration cadence too, at the same
                // interval, so a CDCL(T) search is deadline-bounded on every
                // path and not only on the conflicting one.
                if self.theory_steps.is_multiple_of(DEADLINE_CHECK_INTERVAL)
                    && crate::interrupt::past_deadline(deadline)
                {
                    self.report_progress();
                    return Ok(SearchOutcome::Interrupted);
                }
                // Copy the counters somewhere another thread can read them
                // (see `NativeLayerStatsMirror`). This is the ONLY point at
                // which a search that is killed from outside says anything at
                // all: `native_layer_stats()` is otherwise read once, after
                // `run` returns, which for a timed-out file never happens.
                //
                // Clock-free and off by default: with no mirror installed the
                // whole block is one `Option` test on an already-hot cache
                // line, and the modulo is not even evaluated.
                if self.collect_layer_stats
                    && let Some(mirror) = self.layer_stats_mirror.as_ref()
                    && self
                        .theory_steps
                        .is_multiple_of(LAYER_STATS_MIRROR_INTERVAL)
                {
                    mirror.store(self.native_layer_stats());
                }
            }
            let propagated_conflict = if self.collect_layer_stats {
                let started = Instant::now();
                let conflict = self.propagate();
                self.time_boolean_propagate += started.elapsed();
                conflict
            } else {
                self.propagate()
            };
            if let Some(conflict) = propagated_conflict {
                if let Some(outcome) = self.handle_conflict(conflict, deadline, max_conflicts)? {
                    return Ok(outcome);
                }
            } else {
                // Boolean propagation has reached a fixpoint with no conflict —
                // the CDCL(T) point at which the theory is consulted (ADR-1701
                // slice 2 spike; `NullTheory` makes this a no-op and cannot
                // return `Some`). Placed BEFORE the restart check so a theory
                // sees every assignment on the trail that produced it, and
                // before `reduce_db` can ever run again, so a theory reason
                // clause could not be deleted between being emitted and being
                // used.
                match self.theory_round() {
                    TheoryRound::Stop(outcome) => {
                        self.report_progress();
                        return Ok(outcome);
                    }
                    // A theory conflict: install the lemma as an ADR-1704
                    // input clause, backjump so it is conflicting at the
                    // current level, and hand it to the ordinary 1-UIP path.
                    TheoryRound::Conflict(core) => {
                        let Some(cid) = self.stage_theory_conflict(core) else {
                            self.report_progress();
                            return Ok(SearchOutcome::Interrupted);
                        };
                        if self.collect_layer_stats {
                            self.stat_theory_conflicts += 1;
                        }
                        if let Some(outcome) = self.handle_conflict(cid, deadline, max_conflicts)? {
                            return Ok(outcome);
                        }
                        continue;
                    }
                    // The theory put literals on the trail: hand them to
                    // Boolean propagation before deciding anything else, so a
                    // theory implication is propagated to fixpoint exactly like
                    // a Boolean one.
                    TheoryRound::Propagated => continue,
                    TheoryRound::Fixpoint => {}
                }
                // No conflict: snapshot the target phase if this is the deepest
                // conflict-free assignment yet (the "closest to a model" polarities),
                // then consider a restart (EMA glue by default, Luby fallback) and make
                // a decision.
                if self.use_target_rephase {
                    self.snapshot_target_phase();
                }
                if self.decision_level() > 0 && self.should_restart() {
                    if self.count_search {
                        self.counters.restarts += 1;
                    }
                    self.conflicts_since_restart = 0;
                    self.restart_count += 1;
                    self.backtrack_to(0);
                    // Target phasing (T1.3.1): re-descend toward the deepest
                    // conflict-free assignment seen SINCE THE LAST REPHASE, not
                    // the last-seen polarities. Pure decision-order heuristic.
                    if self.use_target_rephase {
                        self.phase.copy_from_slice(&self.target_phase);
                    }
                    // Scheduled rephase (R6): release the target high-water mark
                    // so the ratchet does not saturate, and install whatever
                    // vector the schedule calls for. Applied AFTER the target
                    // copy, so a rephase both replaces this restart's phases and
                    // opens the next interval. Nothing here is read by the
                    // verdict -- phases only order decisions.
                    //
                    // Confined to stable mode when the mode schedule is on
                    // (Kissat `rephase.c:34-36`); unconditional otherwise,
                    // because with no mode schedule there is no stable half to
                    // confine it to and gating would disable the schedule
                    // instead of halving it.
                    let conflicts = self.conflicts as u64;
                    if self.use_target_rephase && self.phase_policy.should_rephase(conflicts) {
                        if self.restart_policy.rephase_allowed() {
                            let action = self.phase_policy.next_action(conflicts);
                            self.apply_rephase(action);
                        } else if self.count_search {
                            // Deferred, not dropped: `should_rephase` stays true
                            // until it fires, so this rephase happens at the
                            // first restart of the next stable phase. Counting
                            // the refusals is the only way to see the gate
                            // working -- the rephase TOTAL is unchanged by it.
                            self.counters.rephase_deferrals += 1;
                        }
                    }
                    continue;
                }
                // Assumption installation (MiniSat's `search`): while assumption
                // levels remain, the next decision is the next assumption rather
                // than a VSIDS pick. Placed after the restart check and before
                // `pick_branch`, exactly where MiniSat puts it, so a restart that
                // backtracks to level 0 simply re-installs them. With no
                // assumptions the guard is `0 < 0` and the whole block is dead —
                // the one-shot trajectory is unchanged.
                if self.decision_level() < assumptions.len() {
                    let p = assumptions[self.decision_level()];
                    match self.value(p) {
                        // Already true: push an empty decision level so the level
                        // numbering keeps matching the assumption index. No literal
                        // is enqueued, so `propagate` finds nothing and no conflict
                        // can be reported *at* a level like this.
                        Some(true) => {
                            self.push_level();
                        }
                        // Already false: the assumption set is inconsistent with the
                        // clause database. Report the failed-assumption core; this is
                        // NOT a refutation of the formula, so no empty clause is
                        // emitted and no proof step is recorded.
                        Some(false) => {
                            let failed = self.analyze_final(p);
                            self.report_progress();
                            return Ok(SearchOutcome::UnsatUnderAssumptions(failed));
                        }
                        None => {
                            self.push_level();
                            self.enqueue(p, Reason::DECISION);
                        }
                    }
                    continue;
                }
                if let Some(var) = self.pick_branch() {
                    if self.collect_layer_stats {
                        self.stat_decisions += 1;
                    }
                    if self.count_search {
                        self.counters.decisions += 1;
                    }
                    self.push_level();
                    let positive =
                        CnfLit::positive(CnfVar::new(var).expect("variable index in range"));
                    // Phase saving: decide the variable's last-seen polarity.
                    let decision = if self.phase[var] {
                        positive
                    } else {
                        positive.negated()
                    };
                    self.enqueue(decision, Reason::DECISION);
                } else {
                    // Total Boolean assignment: the one moment a theory's
                    // COMPLETE check runs (ADR-1701's `final_check`). It sits
                    // here, after `pick_branch` has exhausted the heap, so it
                    // is reached once per candidate model rather than once per
                    // asserted literal — the whole point of the assert /
                    // final-check split. `NullTheory::final_check` is
                    // `FinalCheckOutcome::Sat`, so `sat` is reported exactly
                    // where it was before.
                    match if T::HAS_THEORY {
                        self.timed_final_check()
                    } else {
                        FinalCheckOutcome::Sat
                    } {
                        FinalCheckOutcome::Sat => {}
                        // `Unknown` is undecided by definition: the theory
                        // could not complete its check, so neither can we.
                        FinalCheckOutcome::Unknown => {
                            self.report_progress();
                            return Ok(SearchOutcome::Interrupted);
                        }
                        // A complete check looks at the whole assignment, so
                        // its core is NOT required to name a current-level
                        // literal. `stage_theory_conflict` backjumps to the
                        // highest level the core names before analysis, or
                        // 1-UIP's path counter underflows (ADR-1701).
                        FinalCheckOutcome::Conflict(explanation) => {
                            let Some(core) = self.materialize_explanation(explanation) else {
                                self.report_progress();
                                return Ok(SearchOutcome::Interrupted);
                            };
                            let Some(cid) = self.stage_theory_conflict(core) else {
                                self.report_progress();
                                return Ok(SearchOutcome::Interrupted);
                            };
                            if self.collect_layer_stats {
                                self.stat_theory_conflicts += 1;
                            }
                            if let Some(outcome) =
                                self.handle_conflict(cid, deadline, max_conflicts)?
                            {
                                return Ok(outcome);
                            }
                            continue;
                        }
                    }
                    let values = self.assign.iter().map(|v| v.unwrap_or(false)).collect();
                    self.report_progress();
                    return Ok(SearchOutcome::Sat(CnfAssignment::new(values)));
                }
            }
        }
    }

    /// The conflict half of [`Cdcl::search_loop`]: analyse `conflict`, emit the
    /// learned clause, backjump and enqueue the asserting literal.
    ///
    /// Returns `Some(outcome)` when the search is over (a refutation, an
    /// exhausted budget, an expired deadline) and `None` to carry on. Split out
    /// of the loop so a **theory** conflict reaches exactly the same code: an
    /// installed theory lemma is a clause id like any other by the time it gets
    /// here, and there is no second learning path that could drift from this
    /// one.
    fn handle_conflict(
        &mut self,
        conflict: CRef,
        deadline: Option<Instant>,
        max_conflicts: usize,
    ) -> Result<Option<SearchOutcome>, ProofSinkError> {
        if self.decision_level() == 0 {
            // The empty clause must be RUP over `cnf ++ lemmas`, and it is only
            // if every level-zero implication the checker has to replay is
            // justified by a clause the artifact carries. A theory implication
            // whose explanation is still a handle is not: it justifies a trail
            // literal with nothing in the database behind it. Materialise those
            // before emitting, or decline (never emit an empty clause we cannot
            // stand behind).
            if T::HAS_THEORY && !self.materialize_trail_theory_reasons() {
                self.report_progress();
                return Ok(Some(SearchOutcome::Interrupted));
            }
            self.record_proof_step(false, &[]);
            self.sink.add_clause(&[])?;
            self.report_progress();
            return Ok(Some(SearchOutcome::Unsat));
        }
        self.conflicts += 1;
        // Tier boundaries are recomputed from the used-glue histogram on a
        // doubling conflict interval (capped at 2^16), so this is O(1)
        // amortized and O(128) on the rare firing conflict.
        if self.db_policy.on_conflict(self.conflicts as u64) {
            let (tier1, tier2) = self.db_policy.tiers.limits();
            if self.count_search {
                self.counters.tier_recomputes += 1;
                self.counters.tier1_limit_last = tier1;
                self.counters.tier2_limit_last = tier2;
                self.counters.tier1_limit_sum += u64::from(tier1);
                self.counters.tier2_limit_sum += u64::from(tier2);
            }
        }
        if self.conflicts > max_conflicts {
            self.report_progress();
            return Ok(Some(SearchOutcome::ResourceOut));
        }
        // Deterministic deadline cadence: only read the clock once every
        // `DEADLINE_CHECK_INTERVAL` conflicts. On expiry, abandon the
        // search with an *undecided* verdict (never sat/unsat by timeout).
        if self.conflicts.is_multiple_of(DEADLINE_CHECK_INTERVAL)
            && crate::interrupt::past_deadline(deadline)
        {
            self.report_progress();
            return Ok(Some(SearchOutcome::Interrupted));
        }
        let (learned, backjump, lbd) = if self.collect_layer_stats {
            let started = Instant::now();
            let analyzed = self.analyze(conflict);
            self.time_conflict_analysis += started.elapsed();
            analyzed
        } else {
            self.analyze(conflict)
        };
        // Update the Glucose EMA restart state from this conflict -- the glue
        // (LBD) averages and the blocking trail average, sampled at the
        // conflict trail (before the backjump below). Only when SOME mode runs
        // the EMA schedule (the default is Luby in both; see
        // `track_restart_emas` for why this is not `use_ema_restart`), so the
        // averages cost nothing on the default path.
        if self.track_restart_emas {
            self.update_restart_emas(lbd);
        }
        // The mode switch, once per analysed conflict. Placed after `analyze`
        // so the tick total it reads includes this conflict's resolution steps
        // and mark array, and before the restart check in the search loop so a
        // switch takes effect at the very next restart decision.
        self.consider_mode_switch();
        self.record_proof_step(false, &learned);
        self.sink.add_clause(&learned)?;
        if learned.is_empty() {
            self.report_progress();
            return Ok(Some(SearchOutcome::Unsat));
        }
        let asserting = learned[0];
        let clause_id = self.alloc_clause(&learned);
        if learned.len() >= 2 {
            let binary = learned.len() == 2;
            self.watches[lit_code(learned[0])].push(Watch::new(clause_id, learned[1], binary));
            self.watches[lit_code(learned[1])].push(Watch::new(clause_id, learned[0], binary));
        }
        // Register the new learned clause's deletion metadata.
        self.lbd.push(lbd);
        self.cla_activity.push(0.0);
        // A freshly learned clause starts with a full lifetime budget: it was
        // just derived from the current conflict, so it is by construction
        // "used" this round.
        self.used.push(self.db_policy.max_used);
        self.deleted.push(false);
        self.learned.push(true);
        self.learned_live += 1;
        self.bump_clause(clause_id);
        self.backtrack_to(backjump);
        self.enqueue(asserting, Reason::clause(clause_id));
        self.conflicts_since_restart += 1;
        self.decay();
        self.decay_clause();
        // Learned-clause-database reduction (Glucose/MiniSat schedule):
        // when the live learned-clause count exceeds the growing budget,
        // delete the worst half (sound: see `reduce_db`). Must run at a
        // point where no decisions are pending so the trail/reasons are
        // consistent; here we are immediately after a backjump+enqueue
        // and before propagation, which is safe (locked-clause check
        // reads the current trail).
        let conflicts = self.conflicts as u64;
        if conflicts >= self.reduce_backoff_until
            && self.db_policy.reduce_due(
                self.learned_live,
                conflicts,
                self.reductions as u64,
                self.next_reduce_conflicts,
            )
        {
            self.reduce_db()?;
            self.reductions += 1;
            self.next_reduce_conflicts = self
                .db_policy
                .next_reduce_limit(conflicts, self.reductions as u64);
        }
        // Observability hook (see `ProofSearchProgress`): a no-op cadence
        // check when no sink is installed. Placed after all per-conflict
        // bookkeeping so a fired snapshot reflects this conflict fully.
        self.maybe_report_progress();
        Ok(None)
    }

    /// Resolves a [`TheoryExplanation`] into the clause it stands for, asking
    /// the theory only when the handle is lazy.
    ///
    /// `None` means the theory could not explain a handle it issued. That is a
    /// theory bug and it is answered with the undecided outcome, never by
    /// treating a missing explanation as an empty clause (which would be a
    /// wrong `unsat`).
    #[cold]
    #[inline(never)]
    fn materialize_explanation(&mut self, explanation: TheoryExplanation) -> Option<Vec<CnfLit>> {
        self.materialize_explanation_of(explanation, None)
    }

    /// [`Cdcl::materialize_explanation`] for a handle whose clause is known to
    /// contain `implied`.
    ///
    /// The distinction is invisible to a theory that materialises its own
    /// clauses and load-bearing for an adapter over a channel that carries
    /// *asserted* literals: a conflict core turns into a clause by negating
    /// every literal, whereas a propagation reason turns into one by negating
    /// every antecedent and then adding the implied literal back. Passing
    /// `None` where a reason was meant drops that literal, and the resulting
    /// clause is stronger than anything the theory entails.
    #[cold]
    #[inline(never)]
    fn materialize_explanation_of(
        &mut self,
        explanation: TheoryExplanation,
        implied: Option<CnfLit>,
    ) -> Option<Vec<CnfLit>> {
        match explanation {
            TheoryExplanation::Eager(lits) => Some(lits),
            TheoryExplanation::Lazy(handle) => {
                if self.collect_layer_stats {
                    let started = Instant::now();
                    let explained = self.theory.explain(handle, implied);
                    self.time_theory_explain += started.elapsed();
                    explained
                } else {
                    self.theory.explain(handle, implied)
                }
            }
        }
    }

    /// [`theory::NativeTheory::final_check`], timed and counted when the
    /// instrument is on. Reached only when `T::HAS_THEORY`.
    fn timed_final_check(&mut self) -> FinalCheckOutcome {
        if self.collect_layer_stats {
            let started = Instant::now();
            let outcome = self.theory.final_check();
            self.time_theory_final_check += started.elapsed();
            self.stat_final_checks += 1;
            outcome
        } else {
            self.theory.final_check()
        }
    }

    /// Prepares a theory conflict clause for 1-UIP analysis: install it as an
    /// ADR-1704 lemma and backjump until it is conflicting at the current
    /// decision level. Returns its [`CRef`], or `None` to decline.
    ///
    /// It declines -- soundly, with the undecided outcome -- in exactly two
    /// cases, both of which are theory-contract violations rather than
    /// verdicts:
    ///
    /// - an **empty** core names nothing to learn from; treating it as the
    ///   empty clause would be a wrong `unsat` on the theory's say-so with no
    ///   clause in the artifact to show for it. `CdclT` declines the same case
    ///   for the same reason.
    /// - a core naming a literal that is not currently **false**. The clause
    ///   would not be conflicting, so `analyze` would resolve against a
    ///   non-antecedent and its path counter would underflow.
    ///
    /// On success the clause is an *input* clause of the extended formula
    /// (`learned[cid] == false`), so `reduce_db` can never delete it, and it is
    /// recorded in [`Cdcl::theory_lemmas`], so the artifact's lemma count moves
    /// with it.
    #[cold]
    #[inline(never)]
    fn stage_theory_conflict(&mut self, core: Vec<CnfLit>) -> Option<CRef> {
        let mut clause: Vec<CnfLit> = Vec::with_capacity(core.len());
        for lit in core {
            if clause.contains(&lit) {
                continue;
            }
            if self.value(lit) != Some(false) {
                return None;
            }
            clause.push(lit);
        }
        if clause.is_empty() {
            return None;
        }
        // Order the two highest-level literals into slots 0 and 1: the watch
        // placement that stays correct for a conflicting clause added under a
        // partial assignment, since a backtrack that unassigns either watched
        // literal unassigns it at or above the clause's own conflict level.
        let mut best = 0;
        for k in 1..clause.len() {
            if self.level[clause[k].var().index()] > self.level[clause[best].var().index()] {
                best = k;
            }
        }
        clause.swap(0, best);
        if clause.len() >= 2 {
            let mut second = 1;
            for k in 2..clause.len() {
                if self.level[clause[k].var().index()] > self.level[clause[second].var().index()] {
                    second = k;
                }
            }
            clause.swap(1, second);
        }
        let conflict_level = self.level[clause[0].var().index()];
        // A complete check's core need not name a current-level literal, so
        // come back up to the deepest level it does name before analysing it
        // (ADR-1701). Every literal stays false: they all sit at or below this
        // level.
        if conflict_level < self.decision_level() {
            self.backtrack_to(conflict_level);
        }
        Some(self.install_theory_lemma_clause(&clause))
    }

    /// Registers `clause` in the arena as an ADR-1704 theory lemma: an **input**
    /// clause (`learned[cid] == false`, so never a `reduce_db` candidate),
    /// watched on slots 0 and 1, and appended to [`Cdcl::theory_lemmas`].
    ///
    /// Nothing is emitted to the DRAT sink: a lemma is an input clause of the
    /// extended formula, not a derived step. Emitting it would be exactly the
    /// unlabelled learned clause ADR-1704 section 5 forbids.
    ///
    /// The caller owns slot placement -- [`Cdcl::install_theory_lemma`] puts
    /// the implied literal first, [`Cdcl::stage_theory_conflict`] puts the two
    /// highest-level literals first -- because the two cases have different
    /// invariants and folding them together would hide that.
    fn install_theory_lemma_clause(&mut self, clause: &[CnfLit]) -> CRef {
        let cid = self.alloc_clause(clause);
        self.lbd.push(0);
        self.cla_activity.push(0.0);
        // Not a learned clause: `reduce_db` can never delete it, so its
        // lifetime counter is never read. Pushed to keep the per-clause vectors
        // index-aligned.
        self.used.push(0);
        self.deleted.push(false);
        // NOT `true`: an input clause, never a `reduce_db` candidate.
        self.learned.push(false);
        if clause.len() >= 2 {
            let binary = clause.len() == 2;
            self.watches[lit_code(clause[0])].push(Watch::new(cid, clause[1], binary));
            self.watches[lit_code(clause[1])].push(Watch::new(cid, clause[0], binary));
        }
        self.theory_lemmas.push(clause.to_vec());
        cid
    }

    /// Resolves every outstanding lazy theory reason on the trail into an
    /// installed input clause. Returns `false` when the theory cannot explain a
    /// handle it issued.
    ///
    /// Called once, immediately before the empty clause is emitted at decision
    /// level zero. Its job is the artifact's, not the search's: `check_drat`
    /// replays unit propagation over `cnf ++ lemmas`, and a trail literal whose
    /// only justification is a handle the theory still holds is invisible to
    /// that replay -- so without this the emitted empty clause could fail to be
    /// RUP through no fault of the search.
    #[cold]
    #[inline(never)]
    fn materialize_trail_theory_reasons(&mut self) -> bool {
        for index in 0..self.trail.len() {
            let var = self.trail[index];
            let Some(handle) = self.reason[var].as_theory() else {
                continue;
            };
            let implied = self.true_literal(var);
            let Some(lits) = self.theory.explain(handle, Some(implied)) else {
                return false;
            };
            let cid = self.install_theory_lemma(implied, &lits);
            self.reason[var] = Reason::clause(cid);
        }
        true
    }

    /// Admits `count` theory atoms registered mid-search (ADR-1701's
    /// `take_new_atoms`), as `count` fresh SAT variables appended after every
    /// existing one.
    ///
    /// The atom-to-variable convention is the one the whole module uses:
    /// [`NativeTheory::assert`]'s `var` **is** the SAT variable index, and new
    /// atoms take the next consecutive indices, so a count is the whole
    /// registration signal and there is no side table to keep aligned.
    ///
    /// Called only from [`Cdcl::theory_round_body`], which runs at a Boolean
    /// propagation fixpoint: nothing is pending, the trail is consistent, and
    /// the new variables are unassigned at level zero with no reason -- the
    /// state every other unassigned variable is in. They are marked branchable
    /// and inserted into the order heap, so the next `pick_branch` can reach
    /// them; without that a registered atom would never be decided and the
    /// search would report `sat` on an assignment that does not mention it.
    #[cold]
    #[inline(never)]
    fn register_theory_atoms(&mut self, count: usize) {
        let base = self.assign.len();
        self.ensure_vars(base + count);
        for var in base..base + count {
            self.branchable[var] = true;
            if !self.heap_contains(var) {
                self.heap_insert(var);
            }
        }
    }

    /// Two-watched-literal unit propagation with **blocking literals** (the
    /// `MiniSat`/`BatSat` BCP). Returns a conflicting clause id, or `None` if the
    /// queue drains with no conflict.
    ///
    /// The watch list of the now-false literal is scanned with an in-place `i`
    /// (read) / `j` (write) compaction (mirroring `BatSat`'s `propagate`):
    ///
    /// 1. If a watch's cached `blocker` is already true, the clause is satisfied;
    ///    keep the watch and skip *without touching the clause array* — the fast
    ///    path that most watches take.
    /// 2. Otherwise dereference the clause, put the false literal at index 1, and:
    ///    - if the other watched literal (index 0) is true, keep the watch
    ///      (refreshing its blocker to that literal) and continue;
    ///    - else look for a non-false replacement literal to watch — if found,
    ///      move the watch to that literal's list (blocker = index-0 literal);
    ///    - else the clause is unit/conflicting: keep the watch (blocker = the
    ///      index-0 literal). If index 0 is false → conflict; otherwise enqueue
    ///      index 0 as a unit implication.
    ///
    /// Blocking literals only reduce the *work* to find propagations/conflicts;
    /// the derived implications and conflicts are identical to the plain scheme.
    fn propagate(&mut self) -> Option<usize> {
        let mut conflict = None;
        while self.qhead < self.trail.len() {
            let var = self.trail[self.qhead];
            self.qhead += 1;
            let false_lit = self.true_literal(var).negated();
            let code = lit_code(false_lit);

            let mut watchers = std::mem::take(&mut self.watches[code]);
            let end = watchers.len();
            let mut i = 0usize;
            let mut j = 0usize;
            'clauses: while i < end {
                let watch = watchers[i];
                if self.count_search {
                    self.counters.watch_visits += 1;
                    // Branchless: the instrumentation for a throughput change
                    // must not cost more on the hot path than the change
                    // saves, and a second conditional here is exactly the
                    // shape that would.
                    self.counters.binary_watch_visits += u64::from(watch.is_binary());
                }
                // (1) Fast path: a true blocker means the clause is satisfied;
                // keep the watch and move on without inspecting the clause.
                let blocker = watch.blocker;
                if self.value(blocker) == Some(true) {
                    watchers[j] = watch;
                    j += 1;
                    i += 1;
                    continue;
                }

                let cid = watch.clause();

                // (1b) Binary fast path: a two-literal clause's blocker IS its
                // other literal, so the watch alone decides the propagation and
                // the clause header and arena are never touched (Kissat
                // `proplit.h:82-93`). Under the pre-2026-09 layout every watch
                // that reached this point dereferenced the clause; that is what
                // `binary_arena_derefs_avoided` counts.
                if watch.is_binary() {
                    if self.count_search {
                        self.counters.binary_arena_derefs_avoided += 1;
                    }
                    watchers[j] = watch;
                    j += 1;
                    i += 1;
                    if self.value(blocker) == Some(false) {
                        conflict = Some(cid);
                        while i < end {
                            watchers[j] = watchers[i];
                            j += 1;
                            i += 1;
                        }
                        break;
                    }
                    if self.count_search {
                        self.counters.propagations += 1;
                    }
                    self.enqueue(blocker, Reason::clause(cid));
                    continue;
                }

                if self.count_search {
                    self.counters.clause_visits += 1;
                }
                // Keep the falsified literal at slot 1 (arena slot offset+1).
                let off = self.headers[cid].offset;
                if self.arena[off] == false_lit {
                    self.arena.swap(off, off + 1);
                }
                i += 1;

                // (2) If the other watched literal is true, the clause is
                // satisfied; keep this watch with its blocker refreshed to it.
                let first = self.arena[off];
                if first != blocker && self.value(first) == Some(true) {
                    watchers[j] = Watch::long(cid, first);
                    j += 1;
                    continue;
                }

                // Look for a non-false literal to watch instead of `false_lit`.
                let len = self.headers[cid].len;
                for k in 2..len {
                    if self.value(self.arena[off + k]) != Some(false) {
                        self.arena.swap(off + 1, off + k);
                        // Move the watch to the new literal's list; its blocker
                        // is the surviving (slot-0) watched literal. This watch
                        // is dropped from the current list (not copied to `j`).
                        let new_code = lit_code(self.arena[off + 1]);
                        self.watches[new_code].push(Watch::long(cid, first));
                        if self.count_search {
                            self.counters.watch_relocations += 1;
                        }
                        continue 'clauses;
                    }
                }

                // No replacement: the clause is unit or conflicting under the
                // current assignment. Keep this watch (blocker = index-0 lit).
                watchers[j] = Watch::long(cid, first);
                j += 1;
                if self.value(first) == Some(false) {
                    // Conflict: stop scanning, but preserve the remaining (not
                    // yet visited) watches by copying them down to `j`.
                    conflict = Some(cid);
                    while i < end {
                        watchers[j] = watchers[i];
                        j += 1;
                        i += 1;
                    }
                    break;
                }
                if self.count_search {
                    self.counters.propagations += 1;
                }
                self.enqueue(first, Reason::clause(cid));
            }
            watchers.truncate(j);
            self.watches[code] = watchers;
            if conflict.is_some() {
                return conflict;
            }
        }
        None
    }

    /// 1-UIP conflict analysis: returns the learned clause (asserting literal at
    /// index 0, second-watch literal at index 1), the backjump level, and the
    /// learned clause's literal-block distance (the number of distinct decision
    /// levels among its literals — the LBD/glue measure). An empty result means
    /// the conflict is implied at level 0 (the empty clause).
    fn analyze(&mut self, conflict: usize) -> (Vec<CnfLit>, usize, usize) {
        let mut seen = vec![false; self.assign.len()];
        if self.count_search {
            self.counters.conflicts += 1;
            self.counters.analyze_mark_bytes += seen.len() as u64;
        }
        let mut lower: Vec<CnfLit> = Vec::new();
        let mut path_count = 0usize;
        let mut pivot_var: Option<usize> = None;
        let mut index = self.trail.len();
        let mut clause_id = conflict;
        let current = self.decision_level();

        loop {
            if self.count_search {
                self.counters.resolutions += 1;
            }
            // Clone the reason clause's literals so we can bump activities while
            // walking it (the borrow checker forbids reading the arena and
            // mutating `self.activity` at once; reason clauses are short).
            let lits = self.lits(clause_id).to_vec();
            // Two independent lifetime signals, both fed once per antecedent.
            // `bump_clause` maintains the decayed activity score (read only by
            // the legacy ranking); `mark_clause_used` refreshes the `used`
            // counter, feeds the tier estimator's histogram, and promotes the
            // clause if its glue has dropped. The tier policy reads only the
            // latter. Both take the clone above, so neither allocates.
            self.bump_clause(clause_id);
            self.mark_clause_used(clause_id, &lits);
            for q in lits {
                let v = q.var().index();
                if Some(v) == pivot_var || seen[v] || self.level[v] == 0 {
                    continue;
                }
                seen[v] = true;
                self.bump_var(v); // VSIDS: bump every variable in the conflict side
                if self.level[v] >= current {
                    path_count += 1;
                } else {
                    lower.push(q);
                }
            }

            let mut found = false;
            while index > 0 {
                index -= 1;
                if seen[self.trail[index]] {
                    found = true;
                    break;
                }
            }
            if !found {
                return (Vec::new(), 0, 0);
            }

            let var = self.trail[index];
            seen[var] = false;
            path_count -= 1;
            pivot_var = Some(var);

            if path_count == 0 {
                let mut learned = Vec::with_capacity(lower.len() + 1);
                learned.push(self.true_literal(var).negated());
                learned.extend(lower);
                if self.collect_layer_stats {
                    self.stat_learned_clauses += 1;
                    self.stat_learned_literals_premin += learned.len() as u64;
                }
                // Recursive (self-subsuming) minimization: drop literals whose
                // negation is implied — through their reason chains — by the rest
                // of the clause. Shrinks the learned clause more aggressively than
                // one-level subsumption (MiniSat ccmin_mode=2): smaller proof
                // steps, faster propagation, lower backjumps, fewer conflicts.
                //
                // At this point `seen[v]` is true exactly for the non-asserting
                // learned-clause variables (`lower`), and false for the asserting
                // literal's variable — the same precondition BatSat relies on.
                self.minimize(&mut learned, &mut seen);
                if self.collect_layer_stats {
                    self.stat_learned_literals += learned.len() as u64;
                }
                // Put the highest-level non-asserting literal at index 1 so the
                // clause watches correctly after backjumping.
                let mut backjump = 0;
                if learned.len() >= 2 {
                    let mut best = 1;
                    for k in 2..learned.len() {
                        if self.level[learned[k].var().index()]
                            > self.level[learned[best].var().index()]
                        {
                            best = k;
                        }
                    }
                    learned.swap(1, best);
                    backjump = self.level[learned[1].var().index()];
                }
                let lbd = self.compute_lbd(&learned);
                return (learned, backjump, lbd);
            }

            // Resolving here is what makes the lazy channel pay: a theory
            // implication that conflict analysis never walks past is never
            // explained at all. When it IS walked, the explanation becomes an
            // input clause of the extended formula (ADR-1704) and the rest of
            // this loop cannot tell it from any other antecedent.
            clause_id = match self.reason[var].as_clause() {
                Some(cid) => cid,
                None => self.resolve_reason(var),
            };
        }
    }

    /// Installs a theory explanation as an **input** clause of the extended
    /// formula and records it in [`Cdcl::theory_lemmas`] (ADR-1704).
    ///
    /// `lits` is the explanation the theory handed back; `implied` is the
    /// literal it justifies. On return, the arena clause has `implied` at slot
    /// 0 and, at slot 1, the currently-false literal of highest decision level
    /// -- the two-watched-literal placement that stays correct for a clause
    /// added under a partial assignment: `implied`'s level is the maximum of
    /// its antecedents' levels, so any backtrack that unassigns slot 0 also
    /// unassigns slot 1, and the watch invariant is restored together.
    ///
    /// The clause is registered with `learned[cid] = false`. That is the
    /// ADR-1704 classification (a theory lemma extends the *input* formula) and
    /// it simultaneously discharges the soundness obligation the slice-2 design
    /// memo section 4.5 names: `reduce_db` only ever considers clauses with
    /// `learned[cid]`, so a theory reason clause can never be deleted out from
    /// under the assigned literal it justifies. The `is_locked` protection is
    /// not relied on here -- the clause is not a deletion candidate at all.
    ///
    /// Nothing is emitted to the DRAT sink: a lemma is an input clause, not a
    /// derived step. Emitting it would be exactly the unlabelled learned clause
    /// ADR-1704 section 5 forbids.
    ///
    /// # Panics
    ///
    /// Panics when the explanation does not contain `implied`, or contains a
    /// literal that is not currently false. Both are theory contract
    /// violations, in the same class as the implication-graph invariants
    /// `analyze` already asserts with `expect`; letting either through would
    /// put a clause into the database that does not justify the assignment it
    /// is the reason for.
    #[cold]
    #[inline(never)]
    fn install_theory_lemma(&mut self, implied: CnfLit, lits: &[CnfLit]) -> CRef {
        let mut clause: Vec<CnfLit> = Vec::with_capacity(lits.len());
        clause.push(implied);
        for &lit in lits {
            if lit == implied || clause.contains(&lit) {
                continue;
            }
            assert!(
                self.value(lit) == Some(false),
                "theory explanation literal {lit:?} for {implied:?} is not false under the \
                 current assignment"
            );
            clause.push(lit);
        }
        assert!(
            lits.contains(&implied),
            "theory explanation for {implied:?} does not contain the literal it explains"
        );
        // Slot 1 := the highest-level false literal, so the watch pair is
        // undone together on backtracking (see the doc comment).
        if clause.len() >= 2 {
            let mut best = 1;
            for k in 2..clause.len() {
                if self.level[clause[k].var().index()] > self.level[clause[best].var().index()] {
                    best = k;
                }
            }
            clause.swap(1, best);
        }
        let cid = self.alloc_clause(&clause);
        self.lbd.push(0);
        self.cla_activity.push(0.0);
        // Not a learned clause: `reduce_db` can never delete it, so its
        // lifetime counter is never read. Pushed to keep the per-clause vectors
        // index-aligned.
        self.used.push(0);
        self.deleted.push(false);
        // NOT `true`: an input clause, never a `reduce_db` candidate.
        self.learned.push(false);
        if clause.len() >= 2 {
            let binary = clause.len() == 2;
            self.watches[lit_code(clause[0])].push(Watch::new(cid, clause[1], binary));
            self.watches[lit_code(clause[1])].push(Watch::new(cid, clause[0], binary));
        }
        self.theory_lemmas.push(clause);
        cid
    }

    /// The antecedent clause of assigned variable `var`, resolving a lazy
    /// theory reason on first use (ADR-1701 slice-2 design memo section 4.4
    /// (ii)).
    ///
    /// For a `Clause` reason this is a load and a shift -- the hot path, and
    /// the only path a `NullTheory` search ever takes. For a `Theory` reason it
    /// calls [`NativeTheory::explain`], installs the answer as an input clause
    /// (see [`Cdcl::install_theory_lemma`]) and **rewrites the reason in
    /// place**, so the handle is resolved at most once per assignment.
    ///
    /// # Panics
    ///
    /// Panics when `var` is a decision (callers check `is_decision` first) or
    /// when the theory cannot resolve a handle it issued. `explain` returning
    /// `None` is documented as a theory bug, never a verdict, and there is no
    /// sound answer to continue with: the literal is on the trail and conflict
    /// analysis needs its antecedent.
    ///
    /// **Out of line and cold on purpose.** Both callers
    /// (`Cdcl::analyze` and [`Cdcl::lit_redundant`]) test `as_clause()`
    /// inline first, so on every `NullTheory` search this function is never
    /// entered at all. Inlining it would drag
    /// [`Cdcl::install_theory_lemma`]'s body into the two hottest loops in the
    /// core for a case they never take.
    #[cold]
    #[inline(never)]
    fn resolve_reason(&mut self, var: usize) -> CRef {
        // Kept as a real arm rather than an `expect`: `analyze_final` reaches
        // here without the caller-side fast path.
        if let Some(cid) = self.reason[var].as_clause() {
            return cid;
        }
        let handle = self.reason[var]
            .as_theory()
            .unwrap_or_else(|| panic!("resolve_reason called on decision variable {var}"));
        let implied = self.true_literal(var);
        let lits = self
            .theory
            .explain(handle, Some(implied))
            .unwrap_or_else(|| panic!("theory failed to explain its own handle {handle:?}"));
        let cid = self.install_theory_lemma(implied, &lits);
        self.reason[var] = Reason::clause(cid);
        cid
    }

    /// `MiniSat`'s `analyzeFinal`, specialised to the assumption case: `p` is an
    /// assumption literal that is currently **false**, and the result is the
    /// subset of the installed assumptions sufficient to falsify it — the
    /// failed-assumption core.
    ///
    /// The walk is the standard one: seed with `p`'s variable, scan the trail
    /// from the top down to the start of decision level 1, and for each seen
    /// variable either record it (when it is a decision — during assumption
    /// installation every decision *is* an assumption) or mark the rest of its
    /// reason clause. Level-0 literals are entailed by the clause database alone
    /// and are excluded both by the `trail_lim[0]` bound and by the explicit
    /// `level > 0` test.
    ///
    /// The returned core is a *claim*, and the incremental wrapper's callers
    /// check it: re-solving under the core alone must still be unsatisfiable.
    fn analyze_final(&mut self, p: CnfLit) -> Vec<CnfLit> {
        let mut failed = vec![p];
        if self.decision_level() == 0 {
            // `p` is false at level 0: the clause database alone entails `not p`,
            // so `p` on its own is the whole core.
            return failed;
        }
        let mut seen = vec![false; self.assign.len()];
        seen[p.var().index()] = true;
        let bound = self.trail_lim[0];
        let mut index = self.trail.len();
        while index > bound {
            index -= 1;
            let var = self.trail[index];
            if !seen[var] {
                continue;
            }
            if self.reason[var].is_decision() {
                failed.push(self.true_literal(var));
            } else {
                // The reason clause is `var`'s implied literal together with
                // its antecedents. The implied literal is identified by
                // VARIABLE rather than by slot 0: that placement holds for a
                // long clause but not for a binary one, whose arena slots
                // `propagate` no longer permutes (see [`Watch`]). A theory
                // reason is resolved into an input clause here exactly as
                // `analyze` resolves it.
                let cid = match self.reason[var].as_clause() {
                    Some(cid) => cid,
                    None => self.resolve_reason(var),
                };
                let len = self.clause_len(cid);
                for slot in 0..len {
                    let q = self.lit_at(cid, slot);
                    let qv = q.var().index();
                    if qv != var && self.level[qv] > 0 {
                        seen[qv] = true;
                    }
                }
            }
            seen[var] = false;
        }
        failed
    }

    /// An abstraction of a variable's decision level as a single-bit mask
    /// (`MiniSat`'s `abstractLevel`). The union of these masks over a clause's
    /// literals lets [`Self::lit_redundant`] short-circuit: a reason literal
    /// whose level-bit is absent from the clause's mask comes from a decision
    /// level unrelated to the clause and therefore cannot be resolved away.
    #[inline]
    fn abstract_level(&self, var: usize) -> u32 {
        1u32 << (self.level[var] & 31)
    }

    /// Recursive (self-subsuming) minimization of a learned clause — `MiniSat`
    /// `ccmin_mode = 2`, mirroring `BatSat`'s `minimize_conflict`.
    ///
    /// A non-asserting literal `l` is dropped when its negation is already
    /// entailed by the remaining clause literals through `l`'s reason chain:
    /// every literal in `reason(l)` must be in the clause (`seen`), fixed at
    /// level 0, or itself recursively redundant. Resolving the clause against
    /// those reason chains keeps it entailed, so the minimized clause is still
    /// RUP and the emitted DRAT step stays checkable. Decision literals (no
    /// reason) are never redundant, and the asserting literal (index 0) is
    /// always kept.
    ///
    /// Precondition: `seen[v]` is true exactly for the non-asserting
    /// learned-clause variables (and false for the asserting literal's
    /// variable). `seen` is owned by [`Self::analyze`] (a per-conflict local)
    /// and discarded when that frame returns, so no state leaks across
    /// conflicts; the result depends only on this conflict's `seen` state, the
    /// reason graph, and the input clause order, hence is deterministic
    /// (identical input ⇒ identical clause ⇒ identical proof structure).
    fn minimize(&mut self, learned: &mut Vec<CnfLit>, seen: &mut [bool]) {
        if learned.len() <= 1 {
            return;
        }
        // Mask of the decision levels present among the non-asserting literals.
        let mut abstract_levels = 0u32;
        for &l in &learned[1..] {
            abstract_levels |= self.abstract_level(l.var().index());
        }
        // Scratch reused across the `lit_redundant` calls in this minimization.
        // `seen` marks set during a *successful* probe are kept (those literals
        // are now known to be in/implied by the clause, which is sound for
        // later probes); a *failed* probe rolls back its own marks. Removed
        // literals stay marked, which is correct and matches BatSat — `seen` is
        // never read again after this conflict.
        let mut stack: Vec<CnfLit> = Vec::new();
        let mut to_clear: Vec<usize> = Vec::new();
        let mut write = 1usize;
        for read in 1..learned.len() {
            let lit = learned[read];
            let v = lit.var().index();
            // Keep `lit` if it is a decision (no reason) or not redundant.
            if self.reason[v].is_decision()
                || !self.lit_redundant(lit, abstract_levels, seen, &mut stack, &mut to_clear)
            {
                learned[write] = lit;
                write += 1;
            }
        }
        learned.truncate(write);
    }

    /// Can literal `p` be removed from the learned clause? Iterative
    /// self-subsumption check (no recursion — an explicit `stack` avoids stack
    /// overflow on deep reason chains), mirroring `BatSat`'s `lit_redundant`.
    ///
    /// `p` is redundant iff, walking its reason chain, every encountered
    /// literal is fixed at level 0, already in the clause (`seen`), or has a
    /// reason and a level present in `abstract_levels` (so it can in turn be
    /// resolved away). The first literal that has no reason, or whose level is
    /// outside `abstract_levels`, makes `p` irredundant — and we roll back every
    /// `seen` mark this call set (recorded in `to_clear`) before returning
    /// `false`, so a failed probe leaves no state behind. On success the marks
    /// set during the walk are retained (the literals are now known redundant),
    /// recorded in `to_clear` for the caller to clear once minimization ends.
    ///
    /// Takes `&mut self` only so an unresolved theory reason can be resolved in
    /// place; the `as_clause` test below keeps every step of a `NullTheory`
    /// walk on the shared-read path, and [`Cdcl::resolve_reason`] is `#[cold]`
    /// and out of line so its body never lands in this loop. A variant that
    /// kept `&self` by handing the unresolved variable back to
    /// [`Cdcl::minimize`] for resolution was written and measured: it made no
    /// difference (see the S6 measurement note), so the simpler form is kept.
    fn lit_redundant(
        &mut self,
        p: CnfLit,
        abstract_levels: u32,
        seen: &mut [bool],
        stack: &mut Vec<CnfLit>,
        to_clear: &mut Vec<usize>,
    ) -> bool {
        stack.clear();
        stack.push(p);
        let top = to_clear.len();
        while let Some(q) = stack.pop() {
            if self.count_search {
                self.counters.redundancy_steps += 1;
            }
            let qv = q.var().index();
            let rid = match self.reason[qv].as_clause() {
                Some(cid) => cid,
                None => self.resolve_reason(qv),
            };
            // Skip the propagated literal itself. It is identified by
            // VARIABLE, not by slot: a long clause keeps it at arena slot 0,
            // but a binary clause's slots are no longer permuted by
            // `propagate` (see [`Watch`]), so its implied literal may sit in
            // either. A clause holds at most one literal per variable
            // (`add_input_clause` de-duplicates, `analyze` builds from a
            // `seen` set), so this skips exactly the one literal a slot index
            // used to.
            for &l in self.lits(rid) {
                let lv = l.var().index();
                if lv == qv {
                    continue;
                }
                if self.level[lv] == 0 || seen[lv] {
                    continue;
                }
                if !self.reason[lv].is_decision()
                    && (self.abstract_level(lv) & abstract_levels) != 0
                {
                    // `l` may itself be redundant: mark it and recurse.
                    seen[lv] = true;
                    stack.push(l);
                    to_clear.push(lv);
                } else {
                    // `l` has no reason or comes from an unrelated decision
                    // level: `p` cannot be removed. Roll back this probe.
                    for &v in &to_clear[top..] {
                        seen[v] = false;
                    }
                    to_clear.truncate(top);
                    return false;
                }
            }
        }
        true
    }

    /// Literal-block distance of a clause: the number of distinct decision
    /// levels among its literals' current assignments. Computed at learning
    /// time (every literal of a freshly learned clause is assigned). LBD = 2
    /// "glue" clauses are the most valuable and are kept permanently.
    fn compute_lbd(&mut self, clause: &[CnfLit]) -> usize {
        // Stamp table rather than sort+dedup: a monotone generation counter and
        // one `u64` per decision level. A level is "already counted for this
        // clause" iff its stamp equals the current generation, so nothing is
        // allocated, nothing is sorted, and nothing has to be cleared
        // afterwards. Values are identical to the sorted-dedup form -- the
        // number of distinct decision levels among the clause's literals -- and
        // that equality is asserted by
        // `tests::stamped_lbd_matches_the_sorted_dedup_definition`.
        self.lbd_generation += 1;
        let generation = self.lbd_generation;
        if self.lbd_stamp.len() < self.level.len() + 1 {
            self.lbd_stamp.resize(self.level.len() + 1, 0);
        }
        let mut distinct = 0usize;
        for lit in clause {
            let level = self.level[lit.var().index()];
            if self.lbd_stamp[level] != generation {
                self.lbd_stamp[level] = generation;
                distinct += 1;
            }
        }
        distinct
    }

    /// Marks a learned clause as *used* this round and feeds the tier
    /// estimator's used-glue histogram; promotes the clause if its glue has
    /// dropped since it was recorded.
    ///
    /// This is the lifetime signal the tier scheme runs on. It fires once per
    /// antecedent in `analyze` — exactly Kissat's `deduce.c` hook — plus once
    /// when the clause is learned.
    ///
    /// Promotion recomputes the glue and only ever *lowers* it. There is no
    /// demotion in either reference: a clause that has once been level-compact
    /// has demonstrated it, and re-raising its glue because the current trail
    /// happens to be fragmented would throw that away. Promotion is what lets a
    /// clause move into tier1 after it was learned deep, which is the mechanism
    /// that makes a glue-derived tier a *lifetime* policy rather than a
    /// birth-order one.
    /// `lits` is the clause's literals, which `analyze` has already cloned for
    /// its own walk — taking them as an argument keeps this off the allocator.
    fn mark_clause_used(&mut self, cid: usize, lits: &[CnfLit]) {
        if !self.learned[cid] || self.deleted[cid] {
            return;
        }
        if self.db_policy.promote_on_use {
            // Every literal of a reason or conflict clause is assigned when
            // `analyze` walks it, so every `level[]` read here is live.
            let glue = self.compute_lbd(lits);
            if glue < self.lbd[cid] {
                self.lbd[cid] = glue;
                if self.count_search {
                    self.counters.clause_promotions += 1;
                }
            }
        }
        #[allow(clippy::cast_possible_truncation)]
        self.db_policy
            .on_clause_used(self.lbd[cid].min(u32::MAX as usize) as u32);
        self.used[cid] = self.db_policy.max_used;
        if self.count_search {
            self.counters.clause_used_marks += 1;
        }
    }

    /// Bumps a learned clause's activity, rescaling all clause activities (and
    /// `cla_inc`) if it overflows the cap (preserving their relative order).
    fn bump_clause(&mut self, cid: usize) {
        if !self.learned[cid] {
            return; // only learned clauses carry activity
        }
        self.cla_activity[cid] += self.cla_inc;
        if self.cla_activity[cid] > CLAUSE_RESCALE_LIMIT {
            // Rescaling problem clauses too is a no-op: they are never bumped,
            // so their activity is 0.0 and `0.0 * CLAUSE_RESCALE == 0.0`.
            for a in &mut self.cla_activity {
                *a *= CLAUSE_RESCALE;
            }
            self.cla_inc *= CLAUSE_RESCALE;
        }
    }

    /// Decays clause activity by growing the bump increment (the `MiniSat`
    /// trick, mirrored for clauses).
    fn decay_clause(&mut self) {
        self.cla_inc /= CLAUSE_DECAY;
    }

    /// Is learned clause `cid` currently the reason (antecedent) for an assigned
    /// literal? Such a clause is LOCKED: deleting it would corrupt the
    /// implication graph, so it must be protected.
    fn is_locked(&self, cid: CRef) -> bool {
        if self.clause_len(cid) == 0 {
            return false;
        }
        // A clause is locked when it is the reason for one of its own
        // literals. For a long clause that literal is at slot 0 by the
        // `propagate` invariant; a binary clause's slots are no longer
        // permuted (see [`Watch`]), so both are checked. Two slots at most:
        // for a longer clause only slot 0 can be the reason, since `propagate`
        // put the implied literal there.
        let head = self.lit_at(cid, 0).var().index();
        if self.assign[head].is_some() && self.reason[head].as_clause() == Some(cid) {
            return true;
        }
        if self.clause_len(cid) != 2 {
            return false;
        }
        let other = self.lit_at(cid, 1).var().index();
        self.assign[other].is_some() && self.reason[other].as_clause() == Some(cid)
    }

    /// One reduce round, driven entirely by [`Cdcl::db_policy`].
    ///
    /// The round has three separable decisions and the search makes none of
    /// them: which clauses are exempt ([`ClauseDbPolicy::classify`]), how the
    /// rest are ordered ([`ClauseDbPolicy::rank`]), and how many of them go
    /// ([`ClauseDbPolicy::delete_count`]). Under the default tier policy this is
    /// a **lifetime** rule: every live learned clause has its `used` counter
    /// decremented, a tier1 clause survives if it was resolved at all since the
    /// previous round, a tier2 clause survives one further round of grace, and
    /// a tier3 clause is always a candidate. Candidates are deleted worst-first
    /// by `(glue desc, size desc)`.
    ///
    /// Note what does *not* appear: clause activity. A decayed activity score
    /// never expires, so a clause resolved heavily long ago outranks one
    /// resolved last round; neither `CaDiCaL` nor Kissat consults it in `reduce`
    /// for that reason. It is still maintained, and
    /// [`ClauseDbPolicy::legacy`] still ranks by it, so the two are A/B
    /// comparable.
    ///
    /// Soundness/completeness: every learned clause was RUP-derived, so the
    /// formula's models are unchanged by deletion; protecting locked clauses
    /// keeps the implication graph intact; the search can re-derive any deleted
    /// clause, so completeness is preserved. Only `learned[cid]` clauses are
    /// ever candidates, so an input clause or a theory lemma can never be
    /// deleted — deleting either would weaken the formula and could produce a
    /// wrong `sat`. Every deletion emits a DRAT `d` step, so the proof stays
    /// checkable no matter what the policy decides; the policy is visible to the
    /// *trajectory* and invisible to the *proof stream's validity*.
    ///
    /// # Errors
    ///
    /// Propagates a [`ProofSinkError`] from the deletion steps; the caller
    /// abandons the search, since a proof missing its deletions would not replay.
    fn reduce_db(&mut self) -> Result<(), ProofSinkError> {
        if self.count_search {
            self.counters.reductions += 1;
        }
        let round = self.reductions as u64 + 1;
        // One pass over the live learned clauses: decrement every lifetime
        // counter, classify against the current tier boundaries, and collect the
        // candidates with their ranking keys. The decrement happens for every
        // live learned clause including the locked and the exempt ones, exactly
        // as in the references -- a clause that is locked this round has still
        // aged, and pretending otherwise would make locked clauses immortal.
        let mut candidates: Vec<(u64, CRef)> = Vec::new();
        // Kissat's `first_reducible` (`reduce.c:37-61`): the scan starts at the
        // lowest clause id that could still be a candidate, not at 0. Input
        // clauses are never deletable and always precede the first learned
        // clause, so on a bit-blasted formula this skips the bulk of the
        // database on every round, and the skipped prefix grows as the oldest
        // learned clauses are deleted.
        let scan_start = self.reduce_scan_start;
        if self.count_search {
            self.counters.reduce_headers_scanned +=
                (self.headers.len().saturating_sub(scan_start)) as u64;
            self.counters.reduce_headers_skipped += scan_start as u64;
        }
        for cid in scan_start..self.headers.len() {
            if !self.learned[cid] || self.deleted[cid] {
                continue;
            }
            let used_before = self.used[cid];
            self.used[cid] = used_before.saturating_sub(1);
            let glue = self.lbd[cid];
            let size = self.clause_len(cid);
            #[allow(clippy::cast_possible_truncation)]
            let glue_u32 = glue.min(u32::MAX as usize) as u32;
            if self.count_search {
                match self.db_policy.tier_of(glue_u32) {
                    Tier::One => self.counters.reduce_tier1_seen += 1,
                    Tier::Two => self.counters.reduce_tier2_seen += 1,
                    Tier::Three => self.counters.reduce_tier3_seen += 1,
                }
            }
            let locked = self.is_locked(cid);
            let reason = self.db_policy.classify(glue_u32, size, used_before, locked);
            if self.count_search {
                match reason {
                    KeepReason::Locked => self.counters.reduce_locked += 1,
                    KeepReason::TooShort => self.counters.reduce_too_short += 1,
                    KeepReason::Tier1Used => self.counters.reduce_kept_tier1 += 1,
                    KeepReason::Tier2Recent => self.counters.reduce_kept_tier2 += 1,
                    KeepReason::PermanentGlue | KeepReason::Candidate => {}
                }
            }
            if reason == KeepReason::Candidate {
                let rank = self.db_policy.rank(glue_u32, size, self.cla_activity[cid]);
                candidates.push((rank, cid));
            }
        }
        if self.count_search {
            self.counters.reduce_candidates += candidates.len() as u64;
        }
        let to_delete = self.db_policy.delete_count(candidates.len(), round);
        if to_delete == 0 {
            // Nothing to do this round. Our reduce trigger is a learned-clause
            // budget rather than a conflict interval, so without a backoff a
            // fully-protected database would re-run this whole scan on every
            // conflict until the budget grew past it.
            if self.count_search {
                self.counters.reduce_empty_rounds += 1;
            }
            self.reduce_backoff_until =
                (self.conflicts as u64).saturating_add(self.db_policy.empty_round_backoff);
            return Ok(());
        }
        // Ascending rank is worst-first under both ranking keys. The clause id
        // tie-break makes the order total (no hash-map or float-equality
        // ambiguity), and because ids increase with age it deletes the OLDER of
        // two otherwise-identical clauses -- the same tie-break CaDiCaL gets
        // from its stable sort.
        candidates.sort_unstable_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
        for &(_, cid) in candidates.iter().take(to_delete) {
            self.deleted[cid] = true;
            self.learned_live -= 1;
            // Emit a DRAT deletion so the proof replays consistently. The
            // checker matches clauses as sets, and this clause was added
            // verbatim, so the stored literals delete it. (The copy is taken
            // first because the arena and the sink are both reached through
            // `self`.)
            let lits = self.lits(cid).to_vec();
            self.record_proof_step(true, &lits);
            self.sink.delete_clause(&lits)?;
        }
        if self.count_search {
            self.counters.reduce_deleted += to_delete as u64;
        }
        self.sweep_watches();
        self.advance_reduce_scan_start();
        Ok(())
    }

    /// Advances [`Cdcl::reduce_scan_start`] past the prefix of clause ids that
    /// can never be deletion candidates again — input clauses (their `learned`
    /// flag is written once at allocation) and already-tombstoned learned ones
    /// (`deleted` is monotone). Called once, after a round has done its
    /// deletions, so the newly tombstoned prefix is included.
    ///
    /// This is trajectory-preserving: every id it skips would have been
    /// skipped by the scan's own `!learned || deleted` guard, so the candidate
    /// set is identical and only the cost of reaching it changes.
    fn advance_reduce_scan_start(&mut self) {
        let mut start = self.reduce_scan_start;
        while start < self.headers.len() && (!self.learned[start] || self.deleted[start]) {
            start += 1;
        }
        self.reduce_scan_start = start;
    }

    /// Restores the watch lists after `reduce_db` tombstoned its deletions, by
    /// whichever sweep [`ClauseDbPolicy::watch_sweep`] selects.
    ///
    /// The two sweeps agree on the resulting *set* of watches and differ in
    /// cost and in per-list order; [`WatchSweep`] documents why the order is
    /// visible to the search.
    fn sweep_watches(&mut self) {
        match self.db_policy.watch_sweep {
            WatchSweep::Rebuild => self.rebuild_watches(),
            WatchSweep::InPlace => self.prune_watches(),
        }
    }

    /// Drops every watch that points at a clause `reduce_db` just tombstoned,
    /// in place, and leaves every surviving watch exactly where it was
    /// ([`WatchSweep::InPlace`]).
    ///
    /// Against [`Cdcl::rebuild_watches`] this removes, per round, a
    /// `headers[cid]` read and two arena reads **per live clause** over the
    /// WHOLE database — input clauses included, and on a bit-blasted formula
    /// those are the overwhelming majority and can never be deleted — plus
    /// clearing and re-growing `2n` lists, which writes every watch entry
    /// rather than read-and-shifting only the survivors.
    ///
    /// It keeps the same watched literals: the two-watched-literal invariant is
    /// maintained by `propagate` itself, so nothing needs re-deriving.
    ///
    /// This is the sweep half of Kissat's `reduce.c:161,183`
    /// (`first_reducible` plus `kissat_sparse_collect`); the scan half is
    /// [`Cdcl::reduce_scan_start`]. We do not compact the arena: our `CRef`s
    /// are stable indices with no relocation map, and tombstoned literals are
    /// never read.
    ///
    /// **Not the default**, despite being strictly cheaper: the reduce sweep is
    /// under 1% of propagation traffic here and the order it preserves cost
    /// conflicts on six of seven corpus instances. [`WatchSweep`] carries the
    /// measurement.
    fn prune_watches(&mut self) {
        let deleted = &self.deleted;
        let mut scanned: u64 = 0;
        for list in &mut self.watches {
            scanned += list.len() as u64;
            list.retain(|w| !deleted[w.clause()]);
        }
        if self.count_search {
            self.counters.reduce_watch_entries_scanned += scanned;
        }
    }

    /// Rebuilds every watch list from scratch over the live (non-deleted)
    /// clauses, watching the first two literals of each
    /// ([`WatchSweep::Rebuild`], the pre-2026-09 sweep and still the default).
    ///
    /// Correct because `propagate` keeps a long clause's watched literals at
    /// arena slots 0 and 1, and both literals of a binary clause are watched:
    /// re-watching the first two literals re-derives the same watch set, in
    /// clause-id order.
    fn rebuild_watches(&mut self) {
        let mut scanned: u64 = 0;
        for w in &mut self.watches {
            scanned += w.len() as u64;
            w.clear();
        }
        if self.count_search {
            self.counters.reduce_watch_entries_scanned += scanned;
        }
        for cid in 0..self.headers.len() {
            if self.deleted[cid] {
                continue;
            }
            let len = self.clause_len(cid);
            if len >= 2 {
                let (l0, l1) = (self.lit_at(cid, 0), self.lit_at(cid, 1));
                // Each watch's blocker is the other watched literal.
                let binary = len == 2;
                self.watches[lit_code(l0)].push(Watch::new(cid, l1, binary));
                self.watches[lit_code(l1)].push(Watch::new(cid, l0, binary));
            }
        }
    }

    fn backtrack_to(&mut self, level: usize) {
        if level < self.trail_lim.len() {
            // Pop the theory in lockstep, one `pop` per level actually removed,
            // BEFORE the trail is truncated — a theory that walks the driver's
            // trail during `pop` must still see the assignments it is undoing.
            if T::HAS_THEORY {
                if self.collect_layer_stats {
                    let started = Instant::now();
                    for _ in level..self.trail_lim.len() {
                        self.theory.pop();
                    }
                    self.time_theory_push_pop += started.elapsed();
                } else {
                    for _ in level..self.trail_lim.len() {
                        self.theory.pop();
                    }
                }
            }
            let bound = self.trail_lim[level];
            while self.trail.len() > bound {
                let var = self.trail.pop().expect("trail not empty above bound");
                self.assign[var] = None;
                self.reason[var] = Reason::DECISION;
                // The variable becomes a branchable candidate again. Re-insert it
                // into the order heap *only* if it was popped out by `pick_branch`
                // (lazy deletion): variables still in the heap stay put, avoiding
                // re-insertion churn. O(log n) per actually-removed variable.
                if self.branchable[var] && !self.heap_contains(var) {
                    self.heap_insert(var);
                }
            }
            self.trail_lim.truncate(level);
        }
        self.qhead = self.trail.len();
        // The theory's cursor can never point past the trail; clamping it here
        // (rather than only inside the `if`) also covers `backtrack_to(level)`
        // at `level == trail_lim.len()`, which is a no-op for the trail.
        if T::HAS_THEORY {
            self.theory_qhead = self.theory_qhead.min(self.trail.len());
        }
    }

    /// Opens a new decision level: one `trail_lim` entry and one theory
    /// backtrack point, always together.
    ///
    /// Every site that used to write `self.trail_lim.push(self.trail.len())`
    /// goes through here, which is what keeps `trail_lim.len()` and the
    /// theory's push depth equal by construction — the invariant
    /// [`Cdcl::backtrack_to`]'s pop count relies on.
    #[inline]
    fn push_level(&mut self) {
        self.trail_lim.push(self.trail.len());
        if T::HAS_THEORY {
            if self.collect_layer_stats {
                let started = Instant::now();
                self.theory.push();
                self.time_theory_push_pop += started.elapsed();
            } else {
                self.theory.push();
            }
        }
    }

    /// One theory round, run when Boolean propagation has reached a fixpoint
    /// with no conflict (ADR-1701 slice 2 spike).
    ///
    /// Tells the theory about every assignment made since the last round, asks
    /// it to propagate into the driver-owned queue, and collects any atoms it
    /// registered. Returns `Some(outcome)` when the search must stop.
    ///
    /// Theory propagations, theory conflicts and dynamic atom registration are
    /// all acted on (plan slice S7).
    ///
    /// A propagation is enqueued with a [`Reason`]: `Lazy` becomes
    /// [`Reason::theory`], resolved only if conflict analysis walks past it;
    /// `Eager` is materialised as an input clause immediately. Either way the
    /// justifying clause enters the database as an ADR-1704 *lemma* -- an input
    /// clause recorded in [`Cdcl::theory_lemmas`] -- so the emitted Boolean
    /// stream is a DRAT proof of `cnf ++ theory_lemmas` and never of `cnf`
    /// alone.
    ///
    /// A conflict -- from `assert`, or from a propagation onto a literal the
    /// Boolean side has already falsified -- comes back as
    /// [`TheoryRound::Conflict`] carrying the conflict clause, which the caller
    /// installs and analyses exactly like a Boolean one. A conflict the theory
    /// cannot substantiate (an empty core, an unresolvable handle) is declined
    /// with the undecided [`SearchOutcome::Interrupted`], never guessed.
    ///
    /// Atoms registered mid-search become fresh SAT variables here, at the one
    /// point in the loop where the trail is at a propagation fixpoint (see
    /// [`Cdcl::register_theory_atoms`]).
    ///
    /// [`NullTheory`] produces none of these, so this returns
    /// [`TheoryRound::Fixpoint`] on every shipping path.
    ///
    /// **Split into a trivial `#[inline(always)]` gate and a separate body**,
    /// and that split is load-bearing rather than stylistic. Design B of the
    /// slice-2 spike measurement rests on `HAS_THEORY` being an associated
    /// CONST, so the whole theory half vanishes at monomorphization for
    /// `NullTheory`. That only happens if the compiler can see the constant
    /// *at the call site*: when the gate and the body lived in one function,
    /// the body's growth (the propagation loop below) pushed it past the
    /// inlining threshold, and `NullTheory`'s "return immediately" turned into
    /// a real call returning a large enum by `sret` on every decision-side
    /// iteration of the search loop -- measured at roughly +3% on
    /// `proof_sat_solve_php_6_7`. With the split the gate always inlines,
    /// `TheoryRound::Fixpoint` is a constant, and the `match` at the call site
    /// folds away.
    // `inline(always)` and not `inline`: the whole point is that the call site
    // sees `T::HAS_THEORY` as a constant, and a hint the optimizer is free to
    // decline would make design B's "measured free" claim depend on an
    // inlining heuristic. See the doc comment above for the measurement.
    #[allow(clippy::inline_always)]
    #[inline(always)]
    fn theory_round(&mut self) -> TheoryRound {
        if !T::HAS_THEORY {
            return TheoryRound::Fixpoint;
        }
        self.theory_round_body()
    }

    /// The body of [`Cdcl::theory_round`], reached only when a theory is
    /// actually attached. See that function for the contract.
    fn theory_round_body(&mut self) -> TheoryRound {
        // Design B of the spike measurement: `HAS_THEORY` is an associated
        // CONST, so for `T = NullTheory` the compiler drops this whole function
        // — including the trail walk, which is the part design A could not
        // make free. Design A (calling the empty hooks unconditionally) measured
        // +5.8% on `proof_sat_solve_php_6_7`; see the design memo. The gate that
        // makes this unreachable for `NullTheory` is in `theory_round`.
        debug_assert!(T::HAS_THEORY, "theory_round gates this on HAS_THEORY");
        // One clock pair around the whole assert run rather than one per
        // literal: the instrument times stage BOUNDARIES, never trail entries.
        let assert_started = self.collect_layer_stats.then(Instant::now);
        while self.theory_qhead < self.trail.len() {
            let var = self.trail[self.theory_qhead];
            self.theory_qhead += 1;
            let value = self.assign[var] == Some(true);
            if let Err(core) = self.theory.assert(var, value) {
                if let Some(started) = assert_started {
                    self.time_theory_assert += started.elapsed();
                }
                // The conflict clause arrives already materialised and at the
                // current decision level, so it goes straight to the caller.
                return TheoryRound::Conflict(core);
            }
        }
        if let Some(started) = assert_started {
            self.time_theory_assert += started.elapsed();
        }
        self.theory_queue.clear();
        if self.collect_layer_stats {
            let started = Instant::now();
            self.theory.propagate_into(&mut self.theory_queue);
            self.time_theory_propagate += started.elapsed();
        } else {
            self.theory.propagate_into(&mut self.theory_queue);
        }
        let mut propagated = false;
        let mut conflict: Option<(TheoryExplanation, CnfLit)> = None;
        // Taken out of the driver-owned queue so the enqueue loop below can
        // hold `&mut self`; the allocation goes straight back afterwards, so
        // the queue is still paid for once per search and not once per round.
        let queued = core::mem::take(&mut self.theory_queue);
        for index in 0..queued.entries().len() {
            let lit = queued.entries()[index].0;
            match self.value(lit) {
                // Already implied by the Boolean side: nothing to do, and no
                // lemma is installed for an implication the CNF already has.
                Some(true) => {}
                // The theory implies a literal the Boolean side has already
                // falsified: a theory conflict in propagation clothing. The
                // reason clause `lit \/ ~antecedents` has EVERY literal false
                // here -- `lit` included -- so it is already the conflict
                // clause and needs no negation.
                Some(false) => {
                    // The handle stands for the REASON clause of `lit`, which
                    // contains `lit`; it is not a bare conflict core. A theory
                    // that materialises clauses itself cannot tell the
                    // difference, but an adapter over a channel that carries
                    // *asserted* literals can and must -- dropping `lit` here
                    // would install `~antecedents` as an ADR-1704 input clause,
                    // and that is not a theory lemma: the theory entails
                    // `antecedents -> lit`, not `~antecedents`. Refuting the
                    // extended formula would then be a wrong `unsat`.
                    conflict = Some((queued.entries()[index].1.clone(), lit));
                    break;
                }
                None => {
                    let reason = match &queued.entries()[index].1 {
                        TheoryExplanation::Lazy(handle) => Reason::theory(*handle),
                        TheoryExplanation::Eager(lits) => {
                            // Cloned so the `&mut self` call below does not
                            // borrow `queued` and `self` at once. Eager is the
                            // non-lazy channel by definition; the copy is the
                            // cost of materialising now instead of never.
                            let lits = lits.clone();
                            Reason::clause(self.install_theory_lemma(lit, &lits))
                        }
                    };
                    self.enqueue(lit, reason);
                    if self.collect_layer_stats {
                        self.stat_theory_propagations += 1;
                    }
                    propagated = true;
                }
            }
        }
        self.theory_queue = queued;
        if let Some((explanation, implied)) = conflict {
            return match self.materialize_explanation_of(explanation, Some(implied)) {
                Some(core) => TheoryRound::Conflict(core),
                // A theory that cannot explain the propagation it just made is
                // a theory bug. Undecided, never a verdict.
                None => TheoryRound::Stop(SearchOutcome::Interrupted),
            };
        }
        let new_atoms = self.theory.take_new_atoms();
        if new_atoms != 0 {
            self.register_theory_atoms(new_atoms);
            // Report progress so the caller re-enters propagation before
            // deciding: a registered atom may be constrained by a lemma the
            // theory installs on the very next round.
            return TheoryRound::Propagated;
        }
        if propagated {
            TheoryRound::Propagated
        } else {
            TheoryRound::Fixpoint
        }
    }

    fn pick_branch(&mut self) -> Option<usize> {
        // Pop roots (highest activity, lowest index on ties) until an unassigned
        // variable surfaces — the canonical MiniSat lazy-deletion order heap.
        // Each `heap_remove_min` is O(log n); assigned roots are discarded (their
        // re-insertion is deferred to `backtrack_to`). When the heap empties with
        // every variable assigned, the formula is satisfied → `None`.
        //
        // This yields exactly the variable the prior O(n) linear scan would have
        // chosen (same highest-activity / lowest-index tie-break), so the search
        // trajectory is unchanged.
        while !self.heap.is_empty() {
            let var = self.heap_remove_min();
            if self.assign[var].is_none() {
                return Some(var);
            }
        }
        None
    }
}

pub mod incremental;

#[cfg(test)]
mod tests {
    // ADR-1703: BatSat is no longer an engine, only a differential referee. The
    // tests below that name it compile ONLY with `--features batsat-reference`
    // and vanish silently without it (a suite that compiles to zero tests still
    // exits 0) -- confirm a NONZERO count when you run them.
    #[cfg(feature = "batsat-reference")]
    use crate::{SatResult, solve_with_rustsat_batsat};

    use super::{
        CRef, Cdcl, DEFAULT_PROOF_SAT_CONFLICT_LIMIT, Duration, Instant, ProofSearchProgress,
        ProofSolveOutcome, Reason, SearchPolicies, StreamingProofOutcome, TheoryProofOutcome,
        WATCH_BYTES_ON_TARGET, Watch, WatchSweep, lit_code, solve_with_drat_proof,
        solve_with_drat_proof_counted, solve_with_drat_proof_mode_traced,
        solve_with_drat_proof_streaming, solve_with_drat_proof_with_limits,
        solve_with_drat_proof_with_limits_and_progress, solve_with_drat_proof_within,
        solve_with_theory_and_drat_proof,
    };
    use crate::{
        CnfClause, CnfFormula, CnfLit, CnfVar, DratSink, ProofSinkError, TextProofSink,
        VecProofSink, check_drat, write_drat,
    };

    fn lit(value: i64) -> CnfLit {
        let var = CnfVar::new(usize::try_from(value.unsigned_abs() - 1).unwrap()).unwrap();
        if value < 0 {
            CnfLit::positive(var).negated()
        } else {
            CnfLit::positive(var)
        }
    }

    fn formula(variable_count: usize, clauses: &[&[i64]]) -> CnfFormula {
        let mut f = CnfFormula::new(variable_count);
        for clause in clauses {
            f.add_clause(CnfClause::new(clause.iter().map(|&v| lit(v)).collect()))
                .unwrap();
        }
        f
    }

    fn assert_unsat_with_checked_proof(f: &CnfFormula) {
        match solve_with_drat_proof(f) {
            ProofSolveOutcome::Unsat(proof) => {
                assert_eq!(check_drat(f, &proof), Ok(true), "DRAT proof must verify");
            }
            other => panic!("expected unsat, got {other:?}"),
        }
    }

    #[test]
    fn unit_contradiction_is_unsat_with_checked_proof() {
        assert_unsat_with_checked_proof(&formula(1, &[&[1], &[-1]]));
    }

    #[test]
    fn full_2x2_is_unsat_with_checked_proof() {
        assert_unsat_with_checked_proof(&formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]));
    }

    #[test]
    fn pigeonhole_3_into_2_is_unsat_with_checked_proof() {
        assert_unsat_with_checked_proof(&formula(
            6,
            &[
                &[1, 2],
                &[3, 4],
                &[5, 6],
                &[-1, -3],
                &[-1, -5],
                &[-3, -5],
                &[-2, -4],
                &[-2, -6],
                &[-4, -6],
            ],
        ));
    }

    #[test]
    fn empty_clause_is_immediately_unsat() {
        assert_unsat_with_checked_proof(&formula(1, &[&[]]));
    }

    #[test]
    fn pigeonhole_4_into_3_is_unsat_with_checked_proof() {
        // 4 pigeons, 3 holes: x_{p,h} = var 3*(p-1)+h. Each pigeon in some hole
        // (4 clauses) + no two pigeons share a hole (3 holes × C(4,2)=6 pairs).
        // Enough conflicts to exercise VSIDS branching and a Luby restart.
        let v = |p: i64, h: i64| 3 * (p - 1) + h;
        let mut clauses: Vec<Vec<i64>> = Vec::new();
        for p in 1..=4 {
            clauses.push(vec![v(p, 1), v(p, 2), v(p, 3)]);
        }
        for h in 1..=3 {
            for p1 in 1..=4 {
                for p2 in (p1 + 1)..=4 {
                    clauses.push(vec![-v(p1, h), -v(p2, h)]);
                }
            }
        }
        let refs: Vec<&[i64]> = clauses.iter().map(Vec::as_slice).collect();
        assert_unsat_with_checked_proof(&formula(12, &refs));
    }

    // -----------------------------------------------------------------------
    // Stable/focused mode switching.
    //
    // These assert on the SCHEDULE, not on the verdict. A verdict assertion
    // passes with the switch disabled -- both arms decide the same formula --
    // so it cannot tell a working mode switch from a dead one.
    // -----------------------------------------------------------------------

    /// A deterministic random 3-SAT instance at the phase transition. Fixed
    /// xorshift, so the formula is a function of `(vars, ratio_tenths, seed)`
    /// and nothing else.
    fn random_3sat(vars: usize, ratio_tenths: usize, seed: u64) -> CnfFormula {
        let mut state = seed | 1;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut f = CnfFormula::new(vars);
        let bound = u64::try_from(vars).unwrap();
        for _ in 0..(vars * ratio_tenths / 10) {
            let mut lits = Vec::with_capacity(3);
            for _ in 0..3 {
                let v = i64::try_from(next() % bound).unwrap() + 1;
                lits.push(if next() & 1 == 0 { lit(v) } else { lit(-v) });
            }
            f.add_clause(CnfClause::new(lits)).unwrap();
        }
        f
    }

    /// The instance the schedule tests run on: hard enough that the search
    /// analyses tens of thousands of conflicts, so several mode phases complete
    /// inside one solve. Pigeonhole rather than random 3-SAT because its
    /// difficulty is structural: a random instance that happens to be easy would
    /// make these tests vacuous, and 90-variable random 3-SAT at ratio 4.3 was
    /// measured deciding in 25 conflicts.
    fn mode_schedule_instance() -> CnfFormula {
        pigeonhole(10)
    }

    /// The default policy must not switch at all. This is the control for every
    /// assertion below: if it fired, "the schedule alternates" would say nothing
    /// about the policy that asked for alternation.
    #[test]
    fn the_default_policy_never_switches_modes() {
        let f = mode_schedule_instance();
        let mut sink = VecProofSink::new();
        let search = solve_with_drat_proof_mode_traced(
            &f,
            None,
            20_000,
            &mut sink,
            &SearchPolicies::default(),
        );
        assert!(
            search.counters.conflicts > 5_000,
            "the fixture must reach the switching regime, saw {} conflicts",
            search.counters.conflicts
        );
        assert_eq!(search.modes.switches, 0);
        assert_eq!(search.counters.mode_switches, 0);
        assert_eq!(search.modes.mode_sequence(), vec!["focused"]);
        assert_eq!(search.modes.stable_ticks, 0);
    }

    /// The schedule itself: starts focused, alternates, and each phase is
    /// budgeted in ticks with the intervals growing.
    #[test]
    fn mode_switching_alternates_from_focused_on_a_growing_tick_budget() {
        let f = mode_schedule_instance();
        let mut sink = VecProofSink::new();
        let search = solve_with_drat_proof_mode_traced(
            &f,
            None,
            20_000,
            &mut sink,
            &SearchPolicies::mode_switching(),
        );
        let modes = &search.modes;
        assert!(
            modes.switches >= 4,
            "the fixture must complete several phases, saw {} switches at {} \
             conflicts / {} ticks",
            modes.switches,
            search.counters.conflicts,
            search.counters.ticks()
        );
        assert_eq!(
            u64::try_from(modes.transitions.len()).unwrap(),
            modes.switches,
            "every switch must be recorded below the truncation cap"
        );
        assert_eq!(
            modes.mode_sequence()[..5],
            ["focused", "stable", "focused", "stable", "focused"],
            "the search must open focused and alternate strictly"
        );
        assert_eq!(modes.switches, search.counters.mode_switches);
        // Both modes did real work: a schedule that "switches" but spends no
        // ticks on one side is not running two policies.
        assert!(modes.focused_ticks > 0 && modes.stable_ticks > 0);
        assert_eq!(
            modes.focused_ticks + modes.stable_ticks,
            search.counters.ticks(),
            "the per-mode split must partition the run's ticks"
        );
        // The first switch is the conflict bootstrap; every later one is a tick
        // budget the previous phase calibrated.
        assert_eq!(modes.transitions[0].at_conflicts, 1_001);
        assert!(modes.transitions[0].phase_ticks > 0);
        // Quadratic growth: the budget granted at each switch never shrinks, and
        // the fourth is strictly larger than the first. The reference's
        // multiplier sequence is `stabphases^2` with `stabphases` advancing only
        // on entry to stable, i.e. 1, 4, 4, 9, 9, 16, ...
        let budgets: Vec<u64> = modes.transitions.iter().map(|t| t.budget_ticks).collect();
        for w in budgets.windows(2) {
            assert!(w[1] >= w[0], "budgets must not shrink: {budgets:?}");
        }
        assert!(
            budgets[3] > budgets[0],
            "budgets must grow across a stable-phase increment: {budgets:?}"
        );
        let unit = budgets[0];
        assert_eq!(
            budgets[..6],
            [unit, 4 * unit, 4 * unit, 9 * unit, 9 * unit, 16 * unit],
            "the multiplier sequence must be the reference's stabphases^2"
        );
    }

    /// A `DratSink` that burns wall time without changing anything the search
    /// reads. Wrapping a solve in it makes the same trajectory take several
    /// times longer, which is the only way to tell a tick-denominated schedule
    /// from a wall-clock one from inside a single-process test.
    struct PacedSink {
        inner: VecProofSink,
        remaining_pauses: usize,
        pause: Duration,
    }

    impl DratSink for PacedSink {
        fn add_clause(&mut self, literals: &[CnfLit]) -> Result<(), ProofSinkError> {
            if self.remaining_pauses > 0 {
                self.remaining_pauses -= 1;
                let until = Instant::now() + self.pause;
                while Instant::now() < until {
                    core::hint::spin_loop();
                }
            }
            self.inner.add_clause(literals)
        }

        fn delete_clause(&mut self, literals: &[CnfLit]) -> Result<(), ProofSinkError> {
            self.inner.delete_clause(literals)
        }
    }

    /// **Determinism.** The mode schedule must be a function of the formula and
    /// the policy, and of nothing else — determinism is a public API promise
    /// here, and a restart schedule that moved with host load would break it
    /// invisibly: the trajectory and therefore the emitted `DRAT` stream would
    /// depend on how busy the machine was.
    ///
    /// The second arm runs the identical search through a sink that deliberately
    /// wastes wall time. Every integer the search counts is unchanged; only the
    /// clock differs. A schedule denominated in `Instant`s cannot survive this;
    /// one denominated in ticks is bit-identical.
    #[test]
    fn the_mode_schedule_does_not_depend_on_how_long_the_search_takes() {
        // A smaller instance than the schedule tests use: the paced arm has to
        // be several times slower than the plain one for the comparison to
        // discriminate, and padding a six-second search by that factor is not
        // worth the gate time.
        let f = pigeonhole(8);
        // A shorter bootstrap than the shipped 1000 conflicts, so several
        // phases complete inside a search small enough to pad. The quantity
        // under test is the schedule's *independence from the clock*, and that
        // does not depend on the interval sizes.
        let policies = SearchPolicies {
            restart: crate::phase_policy::RestartPolicy::mode_switching_after(200),
            ..SearchPolicies::default()
        };
        let budget = 6_000;

        let mut fast = VecProofSink::new();
        let started = Instant::now();
        let quick = solve_with_drat_proof_mode_traced(&f, None, budget, &mut fast, &policies);
        let fast_elapsed = started.elapsed();

        let mut slow = PacedSink {
            inner: VecProofSink::new(),
            remaining_pauses: 5_000,
            pause: Duration::from_micros(500),
        };
        let started = Instant::now();
        let paced = solve_with_drat_proof_mode_traced(&f, None, budget, &mut slow, &policies);
        let slow_elapsed = started.elapsed();

        assert!(
            quick.modes.switches >= 4,
            "a schedule with too few switches cannot discriminate, saw {}",
            quick.modes.switches
        );
        assert!(
            slow_elapsed > fast_elapsed * 2,
            "the paced arm must actually be much slower, else this test cannot \
             tell a clock from a tick meter ({fast_elapsed:?} vs {slow_elapsed:?})"
        );
        assert_eq!(
            quick.modes, paced.modes,
            "the mode schedule moved when only wall time changed"
        );
        assert_eq!(quick.outcome, paced.outcome);
        assert_eq!(quick.counters, paced.counters);
    }

    /// The rephase schedule is confined to stable mode when the mode schedule is
    /// running (Kissat `rephase.c:34-36`), and unconfined when it is not.
    ///
    /// Asserted on `rephase_deferrals`, not on the rephase count.
    /// [`PhasePolicy::should_rephase`] is a threshold that stays true until it
    /// fires, so the gate *defers* a due rephase to the next stable restart
    /// rather than dropping it, and the two arms rephase the same number of
    /// times. Measured before this was understood: 5 and 5. A test on the count
    /// would have passed with the gate deleted.
    #[test]
    fn rephasing_is_confined_to_stable_mode_only_when_modes_switch() {
        let f = mode_schedule_instance();

        let unconfined = SearchPolicies::scheduled_phase();
        let mut sink = VecProofSink::new();
        let a = solve_with_drat_proof_mode_traced(&f, None, 20_000, &mut sink, &unconfined);
        assert_eq!(a.modes.switches, 0, "this arm must not switch modes");
        assert!(
            a.counters.rephases > 0,
            "with no mode schedule the rephase schedule must still run"
        );
        assert_eq!(
            a.counters.rephase_deferrals, 0,
            "with no mode schedule there is no stable half, so nothing may be \
             deferred -- gating here would silently disable `scheduled_phase`"
        );

        let confined = SearchPolicies {
            phase: crate::phase_policy::PhasePolicy::scheduled(),
            ..SearchPolicies::mode_switching()
        };
        let mut sink = VecProofSink::new();
        let b = solve_with_drat_proof_mode_traced(&f, None, 20_000, &mut sink, &confined);
        assert!(b.modes.switches >= 4);
        assert!(
            b.counters.rephase_deferrals > 0,
            "the mode gate must actually refuse focused-mode rephases"
        );
        assert!(
            b.counters.rephases > 0,
            "a deferred rephase must still eventually happen"
        );
    }

    /// Mode switching is a search-order change and must preserve the verdict and
    /// the certificate. `sat` models still satisfy; `unsat` proofs still
    /// `DRAT`-check.
    #[test]
    fn mode_switching_preserves_verdicts_and_certificates() {
        for seed in 0..12u64 {
            let f = random_3sat(24, 43, 0xabc0_0000_0000_0001 + seed * 0x9e37_79b9);
            let baseline = solve_with_drat_proof(&f);
            let mut sink = VecProofSink::new();
            let switched = solve_with_drat_proof_mode_traced(
                &f,
                None,
                DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
                &mut sink,
                &SearchPolicies::mode_switching(),
            );
            match (&baseline, &switched.outcome) {
                (ProofSolveOutcome::Sat(_), StreamingProofOutcome::Sat(model)) => {
                    assert!(
                        model.satisfies(&f).unwrap(),
                        "seed {seed}: model must satisfy"
                    );
                }
                (ProofSolveOutcome::Unsat(_), StreamingProofOutcome::Unsat) => {
                    assert_eq!(
                        check_drat(&f, &sink.into_steps()),
                        Ok(true),
                        "seed {seed}: unsat proof must DRAT-check"
                    );
                }
                (a, b) => panic!("seed {seed}: verdict moved: {a:?} vs {b:?}"),
            }
        }
    }

    #[test]
    fn satisfiable_formula_yields_a_satisfying_model() {
        let f = formula(3, &[&[1, 2], &[-1, 3], &[-2, -3]]);
        match solve_with_drat_proof(&f) {
            ProofSolveOutcome::Sat(model) => assert!(model.satisfies(&f).unwrap()),
            other => panic!("expected sat, got {other:?}"),
        }
    }

    #[test]
    fn explicit_zero_conflict_limit_returns_resource_out() {
        let f = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
        assert_eq!(
            solve_with_drat_proof_with_limits(&f, None, 0),
            ProofSolveOutcome::ResourceOut
        );
    }

    /// A pigeonhole-4-into-3 fixture: guaranteed unsat and forces enough
    /// conflicts to exercise VSIDS branching, restarts, and (with the tests
    /// below) several progress-sink polls.
    fn pigeonhole_4_into_3() -> CnfFormula {
        let v = |p: i64, h: i64| 3 * (p - 1) + h;
        let mut clauses: Vec<Vec<i64>> = Vec::new();
        for p in 1..=4 {
            clauses.push(vec![v(p, 1), v(p, 2), v(p, 3)]);
        }
        for h in 1..=3 {
            for p1 in 1..=4 {
                for p2 in (p1 + 1)..=4 {
                    clauses.push(vec![-v(p1, h), -v(p2, h)]);
                }
            }
        }
        let refs: Vec<&[i64]> = clauses.iter().map(Vec::as_slice).collect();
        formula(12, &refs)
    }

    /// Control: [`Cdcl::record_proof_step`] is a no-op — the counters it would
    /// otherwise update never move — when no progress sink is installed. This
    /// is the guard the "zero cost when disabled" requirement rests on; delete
    /// the `is_none` early return inside it and this test is the one that
    /// dies (see the report's mutation table).
    #[test]
    fn record_proof_step_is_a_no_op_without_an_installed_sink() {
        let f = formula(2, &[&[1, 2]]);
        let mut sink = VecProofSink::new();
        let mut cdcl = Cdcl::new(&f, &mut sink);
        cdcl.record_proof_step(false, &[lit(1), lit(2)]);
        cdcl.record_proof_step(true, &[lit(1)]);
        assert_eq!(
            cdcl.proof_steps, 0,
            "no sink installed: proof_steps must not move"
        );
        assert_eq!(
            cdcl.proof_bytes, 0,
            "no sink installed: proof_bytes must not move"
        );
    }

    /// The progress sink actually fires, and its cumulative totals agree
    /// exactly with the ground truth the (unrelated) `VecProofSink` +
    /// `write_drat` path independently produces: `proof_steps` matches the
    /// returned proof's length, and `proof_bytes` matches the exact length of
    /// its serialized DRAT text. `progress_interval = 1` polls every conflict,
    /// so on a fixture that needs several conflicts the sink must fire more
    /// than once, with non-decreasing totals throughout.
    #[test]
    fn progress_sink_fires_and_reports_totals_matching_the_proof() {
        let f = pigeonhole_4_into_3();
        let mut snapshots: Vec<ProofSearchProgress> = Vec::new();
        let mut record = |p: &ProofSearchProgress| snapshots.push(*p);
        let outcome = solve_with_drat_proof_with_limits_and_progress(
            &f,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            1,
            &mut record,
        );
        let ProofSolveOutcome::Unsat(proof) = outcome else {
            panic!("expected unsat, got {outcome:?}");
        };
        assert_eq!(check_drat(&f, &proof), Ok(true));
        assert!(
            snapshots.len() > 1,
            "an installed sink polled every conflict on a multi-conflict \
             instance must fire more than once, got {}",
            snapshots.len()
        );
        for pair in snapshots.windows(2) {
            assert!(pair[1].conflicts >= pair[0].conflicts);
            assert!(pair[1].proof_steps >= pair[0].proof_steps);
            assert!(pair[1].proof_bytes >= pair[0].proof_bytes);
            assert!(pair[1].elapsed >= pair[0].elapsed);
        }
        let last = snapshots.last().expect("at least one snapshot");
        assert_eq!(
            last.proof_steps,
            proof.len(),
            "final proof_steps must match the returned proof's step count exactly"
        );
        assert_eq!(
            last.proof_bytes,
            write_drat(&proof).len() as u64,
            "final proof_bytes must match the exact serialized DRAT length"
        );
        assert!(last.conflicts > 0);
    }

    /// [`solve_with_drat_proof_counted`] is claimed in its own documentation to
    /// leave the verdict and the DRAT stream untouched. That is the property
    /// that makes it usable as an A/B instrument at all, so it is asserted
    /// rather than asserted-in-prose: the counted run's proof must be
    /// **byte-identical** to the uncounted one's, not merely also checkable.
    #[test]
    fn counting_does_not_change_the_verdict_or_the_proof() {
        let f = pigeonhole_4_into_3();

        let mut uncounted = VecProofSink::new();
        let plain = solve_with_drat_proof_streaming(
            &f,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            &mut uncounted,
        );
        let mut counted_sink = VecProofSink::new();
        let (counted, counters) = solve_with_drat_proof_counted(
            &f,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            &mut counted_sink,
        );

        assert!(matches!(plain, StreamingProofOutcome::Unsat));
        assert!(matches!(counted, StreamingProofOutcome::Unsat));
        assert_eq!(
            write_drat(&uncounted.into_steps()),
            write_drat(&counted_sink.into_steps()),
            "enabling counters changed the emitted DRAT proof; the counters are \
             supposed to be pure output"
        );
        // A vacuous version of this test would pass with every counter stuck at
        // zero, which is exactly the failure mode this repository warns about,
        // so the counters must also be alive.
        assert!(counters.conflicts > 0, "no conflicts counted");
        assert!(counters.watch_visits > 0, "no watch visits counted");
    }

    /// Every counter is either alive on a real search or is a documented
    /// zero, and the ones that stand in a fixed arithmetic relation to each
    /// other hold it. Derives its expectations from the search rather than
    /// from literals, so it measures the core and not the author's memory.
    #[test]
    fn search_counters_are_alive_and_internally_consistent() {
        let f = pigeonhole_4_into_3();
        let mut sink = VecProofSink::new();
        let (outcome, c) =
            solve_with_drat_proof_counted(&f, None, DEFAULT_PROOF_SAT_CONFLICT_LIMIT, &mut sink);
        assert!(matches!(outcome, StreamingProofOutcome::Unsat));

        for (name, value) in [
            ("conflicts", c.conflicts),
            ("decisions", c.decisions),
            ("propagations", c.propagations),
            ("watch_visits", c.watch_visits),
            ("clause_visits", c.clause_visits),
            ("resolutions", c.resolutions),
            ("analyze_mark_bytes", c.analyze_mark_bytes),
        ] {
            assert!(value > 0, "counter `{name}` never fired on a real search");
        }

        assert!(
            c.clause_visits <= c.watch_visits,
            "a clause can only be dereferenced from a watch that was visited: \
             {} clause visits vs {} watch visits",
            c.clause_visits,
            c.watch_visits
        );
        assert!(
            c.resolutions >= c.conflicts,
            "every conflict walks at least one antecedent: {} resolutions over \
             {} conflicts",
            c.resolutions,
            c.conflicts
        );
        // The headline structural fact this counter exists to expose: `analyze`
        // zeroes one byte per VARIABLE per conflict, whatever the conflict
        // touched. Derived from the formula, not written down.
        assert_eq!(
            c.analyze_mark_bytes,
            c.conflicts * f.variable_count() as u64,
            "`analyze`'s mark array is `vec![false; variables]` per conflict, so \
             its byte total must be exactly conflicts x variables"
        );
    }

    /// The conflict-count cadence in [`Cdcl::maybe_report_progress`] is honored:
    /// a huge interval (bigger than the whole search needs) yields exactly the
    /// one terminal snapshot every search gets regardless of cadence, while
    /// `interval = 1` on the same fixture yields several. This is the guard
    /// that would go silently unexercised if `maybe_report_progress` always
    /// reported once a sink was installed, no matter the interval.
    #[test]
    fn progress_sink_honors_the_configured_interval() {
        let f = pigeonhole_4_into_3();

        let mut sparse: Vec<ProofSearchProgress> = Vec::new();
        let mut record_sparse = |p: &ProofSearchProgress| sparse.push(*p);
        let outcome_sparse = solve_with_drat_proof_with_limits_and_progress(
            &f,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            1_000_000, // far more than this fixture's conflicts
            &mut record_sparse,
        );
        assert!(matches!(outcome_sparse, ProofSolveOutcome::Unsat(_)));
        assert_eq!(
            sparse.len(),
            1,
            "an interval larger than the whole search must yield only the \
             terminal report, got {} snapshots",
            sparse.len()
        );

        let mut dense: Vec<ProofSearchProgress> = Vec::new();
        let mut record_dense = |p: &ProofSearchProgress| dense.push(*p);
        let outcome_dense = solve_with_drat_proof_with_limits_and_progress(
            &f,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            1,
            &mut record_dense,
        );
        assert!(matches!(outcome_dense, ProofSolveOutcome::Unsat(_)));
        assert!(
            dense.len() > sparse.len(),
            "interval=1 must produce strictly more snapshots than a huge \
             interval on the same fixture: dense={} sparse={}",
            dense.len(),
            sparse.len()
        );
    }

    /// The behaviour-preservation guarantee the progress sink's doc comment
    /// makes: installing a sink (any interval) must not change the verdict or
    /// the emitted DRAT proof, on both a `sat` and an `unsat` fixture. Compares
    /// against the plain non-progress entry point, byte for byte / bit for bit.
    #[test]
    fn progress_sink_does_not_change_the_verdict_or_proof() {
        // Unsat fixture.
        let unsat = pigeonhole_4_into_3();
        let plain =
            solve_with_drat_proof_with_limits(&unsat, None, DEFAULT_PROOF_SAT_CONFLICT_LIMIT);
        let mut ticks = 0usize;
        let mut count = |_: &ProofSearchProgress| ticks += 1;
        let with_sink = solve_with_drat_proof_with_limits_and_progress(
            &unsat,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            1,
            &mut count,
        );
        assert_eq!(
            plain, with_sink,
            "installing a progress sink must not change the outcome"
        );
        assert!(ticks > 0, "the sink must actually have been invoked");

        // Sat fixture.
        let sat = formula(3, &[&[1, 2], &[-1, 3], &[-2, -3]]);
        let plain_sat =
            solve_with_drat_proof_with_limits(&sat, None, DEFAULT_PROOF_SAT_CONFLICT_LIMIT);
        let mut sink_calls = 0usize;
        let mut count_sat = |_: &ProofSearchProgress| sink_calls += 1;
        let with_sink_sat = solve_with_drat_proof_with_limits_and_progress(
            &sat,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            1,
            &mut count_sat,
        );
        assert_eq!(plain_sat, with_sink_sat);
    }

    /// Strong validation of the watched-literal core: on many random CNFs, the
    /// CDCL core must agree with the `BatSat` adapter on sat/unsat, every `sat`
    /// model must satisfy, and every `unsat` proof must pass the DRAT checker.
    #[test]
    #[cfg(feature = "batsat-reference")]
    fn random_cnfs_agree_with_batsat_and_self_check() {
        let mut state = 0x1234_5678_9abc_def0u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let below = |n: &mut dyn FnMut() -> u64, bound: u64| usize::try_from(n() % bound).unwrap();
        for _ in 0..400 {
            let vars = 3 + below(&mut next, 5); // 3..=7 variables
            let clause_count = 3 + below(&mut next, 18);
            let mut f = CnfFormula::new(vars);
            let vars_bound = u64::try_from(vars).unwrap();
            for _ in 0..clause_count {
                let width = 1 + below(&mut next, 3); // 1..=3 literals
                let mut lits = Vec::new();
                for _ in 0..width {
                    let v = i64::try_from(next() % vars_bound).unwrap() + 1;
                    let signed = if next() & 1 == 0 { v } else { -v };
                    lits.push(lit(signed));
                }
                f.add_clause(CnfClause::new(lits)).unwrap();
            }

            let batsat = solve_with_rustsat_batsat(&f).unwrap();
            match (solve_with_drat_proof(&f), batsat) {
                (ProofSolveOutcome::Sat(model), SatResult::Sat(_)) => {
                    assert!(model.satisfies(&f).unwrap(), "cdcl model must satisfy");
                }
                (ProofSolveOutcome::Unsat(proof), SatResult::Unsat(_)) => {
                    assert_eq!(check_drat(&f, &proof), Ok(true), "cdcl proof must verify");
                }
                (cdcl, other) => {
                    panic!("cdcl/batsat disagreement: cdcl={cdcl:?} batsat={other:?}");
                }
            }
        }
    }

    /// A generous (already-passed) deadline does not change the verdict: the
    /// deadline-bounded entry decides the same satisfiable/unsatisfiable formulas
    /// the unbounded entry does.
    #[test]
    fn generous_deadline_does_not_change_verdict() {
        let far = Instant::now().checked_add(std::time::Duration::from_secs(3600));
        // Unsat fixture.
        let unsat = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
        assert!(matches!(
            solve_with_drat_proof_within(&unsat, far),
            ProofSolveOutcome::Unsat(_)
        ));
        // Sat fixture.
        let sat = formula(3, &[&[1, 2], &[-1, 3], &[-2, -3]]);
        let ProofSolveOutcome::Sat(model) = solve_with_drat_proof_within(&sat, far) else {
            panic!("expected sat under a far deadline");
        };
        assert!(model.satisfies(&sat).unwrap());
    }

    /// An already-expired deadline yields `Interrupted` — an *undecided* verdict,
    /// never a wrong sat/unsat — on a formula that needs at least one conflict.
    /// (Trivial level-0 unit/empty-clause cases short-circuit before the conflict
    /// loop, so the fixture must force real search past the first conflict.)
    #[test]
    fn expired_deadline_yields_interrupted_never_a_wrong_verdict() {
        // Pigeonhole 4-into-3 forces many conflicts; with a deadline already in
        // the past, the core stops at the first cadence check without deciding.
        let v = |p: i64, h: i64| 3 * (p - 1) + h;
        let mut clauses: Vec<Vec<i64>> = Vec::new();
        for p in 1..=4 {
            clauses.push(vec![v(p, 1), v(p, 2), v(p, 3)]);
        }
        for h in 1..=3 {
            for p1 in 1..=4 {
                for p2 in (p1 + 1)..=4 {
                    clauses.push(vec![-v(p1, h), -v(p2, h)]);
                }
            }
        }
        let refs: Vec<&[i64]> = clauses.iter().map(Vec::as_slice).collect();
        let f = formula(12, &refs);

        let past = Instant::now()
            .checked_sub(std::time::Duration::from_secs(1))
            .expect("clock far enough from epoch");
        // The cadence is every DEADLINE_CHECK_INTERVAL conflicts, so this larger
        // instance reaches a check before finishing; the verdict is Interrupted.
        match solve_with_drat_proof_within(&f, Some(past)) {
            ProofSolveOutcome::Interrupted => {}
            // The instance is genuinely unsat, so deciding it before the first
            // cadence check is also acceptable (just not a *wrong* verdict).
            ProofSolveOutcome::Unsat(proof) => {
                assert_eq!(check_drat(&f, &proof), Ok(true));
            }
            other => panic!("expired deadline must never yield sat: got {other:?}"),
        }
    }

    /// Determinism: the same formula produces byte-identical outcomes across runs
    /// (no hashmap iteration order in the core, no nondeterministic branching).
    #[test]
    fn solve_is_deterministic() {
        let f = formula(
            6,
            &[
                &[1, 2, 3],
                &[-1, 4],
                &[-2, -4, 5],
                &[-3, -5, 6],
                &[-6, 1],
                &[2, -3, -4],
            ],
        );
        let a = solve_with_drat_proof(&f);
        let b = solve_with_drat_proof(&f);
        assert_eq!(a, b, "same input must yield same output");
    }

    /// One-level reference for the comparison test below: a literal is dropped
    /// only if *every* literal of its reason is already in the learned clause
    /// (or level 0). This is the pre-recursion behavior; recursive minimization
    /// must remove a (strict) superset of these literals.
    fn minimize_one_level<S: DratSink>(cdcl: &Cdcl<'_, S>, learned: &mut Vec<CnfLit>) {
        if learned.len() <= 1 {
            return;
        }
        let mut in_learned = vec![false; cdcl.assign.len()];
        for &l in learned.iter() {
            in_learned[l.var().index()] = true;
        }
        let asserting_var = learned[0].var().index();
        learned.retain(|&l| {
            let v = l.var().index();
            if v == asserting_var {
                return true;
            }
            match cdcl.reason[v].kind() {
                super::ReasonKind::Decision | super::ReasonKind::Theory(_) => true,
                super::ReasonKind::Clause(rid) => !cdcl.lits(rid).iter().all(|&q| {
                    let qv = q.var().index();
                    qv == v || in_learned[qv] || cdcl.level[qv] == 0
                }),
            }
        });
    }

    /// Recursive minimization must remove *more* literals than one-level
    /// self-subsumption on a clause whose redundancy is only visible through a
    /// two-step reason chain — and the literal it removes must genuinely be
    /// implied (verified by replaying the resulting unsat proof end-to-end in
    /// the companion test). Reason graph (all at level 1, the same decision):
    ///   uip=v0, a=v1, b=v2, c=v3, learned = [~v0, ~v1, ~v2].
    ///   reason(v2) = [~v2, v3]   (so b is implied by ¬c, c ∉ clause)
    ///   reason(v3) = [~v3, v1]   (so c is implied by ¬a, a ∈ clause)
    /// One-level keeps ~v2 (its reason contains c ∉ clause). Recursive sees that
    /// c is itself redundant (its only non-clause reason literal, a, is in the
    /// clause), so ~v2 is redundant too.
    #[test]
    fn recursive_minimization_removes_more_than_one_level() {
        // The clauses double as the reason clauses; literal at slot 0 of each is
        // the propagated literal that `lit_redundant` skips.
        let neg = |v: usize| CnfLit::positive(CnfVar::new(v).unwrap()).negated();
        // clause 0: reason(v2) = [~v2, v3]; clause 1: reason(v3) = [~v3, v1].
        let f = formula(4, &[&[-3, 4], &[-4, 2]]);
        let mut sink = VecProofSink::new();
        let mut cdcl = Cdcl::new(&f, &mut sink);
        // Hand-build the implication graph at decision level 1 (minimize reads
        // only `level` and `reason`, so leaving `assign` untouched is fine).
        for v in 0..4 {
            cdcl.level[v] = 1;
        }
        cdcl.reason[0] = Reason::DECISION; // uip: kept regardless
        cdcl.reason[1] = Reason::DECISION; // a: a decision literal — never redundant, always kept
        cdcl.reason[2] = Reason::clause(0); // b's reason is clause 0 = [~v2, v3]
        cdcl.reason[3] = Reason::clause(1); // c's reason is clause 1 = [~v3, v1]

        let learned_init = vec![neg(0), neg(1), neg(2)];

        // One-level keeps ~v2 (3 literals remain).
        let mut one = learned_init.clone();
        minimize_one_level(&cdcl, &mut one);
        assert_eq!(one.len(), 3, "one-level cannot remove ~v2 here");

        // Recursive removes ~v2 (2 literals remain: ~v0, ~v1).
        let mut rec = learned_init.clone();
        // `seen` precondition: non-asserting learned vars (1,2) marked.
        let mut seen = vec![false; cdcl.assign.len()];
        seen[1] = true;
        seen[2] = true;
        cdcl.minimize(&mut rec, &mut seen);
        assert_eq!(
            rec,
            vec![neg(0), neg(1)],
            "recursive minimization must drop ~v2 via the v3 reason chain"
        );
        assert!(
            rec.len() < one.len(),
            "recursive must remove strictly more than one-level"
        );
    }

    /// End-to-end soundness for recursive minimization: a battery of random
    /// unsat CNFs (where the recursive scheme is exercised) must still produce
    /// DRAT proofs that the independent checker accepts — i.e. recursively
    /// minimized learned clauses stay RUP. Pairs with the disagree-zero
    /// batteries above (which already run the recursive path on every conflict).
    #[test]
    fn recursive_minimization_keeps_proofs_drat_checkable() {
        let mut state = 0x05ee_d5a7_1234_abcdu64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut unsat_seen = 0u32;
        for _ in 0..400 {
            let vars = 3 + usize::try_from(next() % 5).unwrap(); // 3..=7
            let clause_count = 6 + usize::try_from(next() % 20).unwrap();
            let mut f = CnfFormula::new(vars);
            let vb = u64::try_from(vars).unwrap();
            for _ in 0..clause_count {
                let mut lits = Vec::new();
                for _ in 0..3 {
                    let v = i64::try_from(next() % vb).unwrap() + 1;
                    lits.push(lit(if next() & 1 == 0 { v } else { -v }));
                }
                f.add_clause(CnfClause::new(lits)).unwrap();
            }
            if let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&f) {
                assert_eq!(
                    check_drat(&f, &proof),
                    Ok(true),
                    "recursively minimized proof must DRAT-check"
                );
                unsat_seen += 1;
            }
        }
        assert!(unsat_seen > 0, "battery must include unsat instances");
    }

    /// Soundness stress: ≥100 small random 3-CNFs, fixed seed. The native core
    /// and `BatSat` must never disagree (`DISAGREE = 0`), every native `sat` model
    /// must satisfy, every native `unsat` must DRAT-check.
    #[test]
    #[cfg(feature = "batsat-reference")]
    fn random_3cnf_agreement_stress_disagree_zero() {
        let mut state = 0x0bad_c0de_dead_beefu64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let below = |n: &mut dyn FnMut() -> u64, bound: u64| usize::try_from(n() % bound).unwrap();
        for _ in 0..200 {
            let vars = 4 + below(&mut next, 6); // 4..=9 variables
            let clause_count = 5 + below(&mut next, 25);
            let mut f = CnfFormula::new(vars);
            let vars_bound = u64::try_from(vars).unwrap();
            for _ in 0..clause_count {
                let mut lits = Vec::new();
                for _ in 0..3 {
                    let v = i64::try_from(next() % vars_bound).unwrap() + 1;
                    let signed = if next() & 1 == 0 { v } else { -v };
                    lits.push(lit(signed));
                }
                f.add_clause(CnfClause::new(lits)).unwrap();
            }
            let batsat = solve_with_rustsat_batsat(&f).unwrap();
            match (solve_with_drat_proof(&f), batsat) {
                (ProofSolveOutcome::Sat(model), SatResult::Sat(_)) => {
                    assert!(
                        model.satisfies(&f).unwrap(),
                        "native sat model must satisfy"
                    );
                }
                (ProofSolveOutcome::Unsat(proof), SatResult::Unsat(_)) => {
                    assert_eq!(
                        check_drat(&f, &proof),
                        Ok(true),
                        "native unsat must DRAT-check"
                    );
                }
                (native, other) => {
                    panic!("DISAGREE: native={native:?} batsat={other:?}");
                }
            }
        }
    }

    /// The EMA (Glucose) restart schedule (T1.3.2, [`SearchPolicies::ema_restart`])
    /// is a pure search-order change: it must preserve every verdict. Over harder
    /// random CNFs near the 3-SAT phase transition (~4.2 clauses/var — enough
    /// conflicts to pass the EMA warmup and actually fire glue restarts, unlike the
    /// tiny instances above), the EMA-driven core agrees with `BatSat` on every
    /// instance (`DISAGREE = 0`), every `sat` model satisfies, and every `unsat`
    /// proof DRAT-checks — the same soundness net as the default Luby schedule. This
    /// keeps the (default-off) EMA path covered.
    ///
    /// It now drives the core through the **production** policy rather than by
    /// assigning the private `use_ema_restart` field, which is what this test
    /// used to do and was, until 2026-09-09, the only assignment of `true` to
    /// that field anywhere in the crate.
    #[test]
    #[cfg(feature = "batsat-reference")]
    fn ema_restart_schedule_agrees_with_batsat_disagree_zero() {
        let mut state = 0xe1a5_7a27_c0ff_ee42u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let below = |n: &mut dyn FnMut() -> u64, bound: u64| usize::try_from(n() % bound).unwrap();
        for _ in 0..60 {
            let vars = 16 + below(&mut next, 12); // 16..=27 variables
            let clause_count = vars * 42 / 10; // ~4.2 clauses/var (phase transition)
            let mut f = CnfFormula::new(vars);
            let vars_bound = u64::try_from(vars).unwrap();
            for _ in 0..clause_count {
                let mut lits = Vec::new();
                for _ in 0..3 {
                    let v = i64::try_from(next() % vars_bound).unwrap() + 1;
                    let signed = if next() & 1 == 0 { v } else { -v };
                    lits.push(lit(signed));
                }
                f.add_clause(CnfClause::new(lits)).unwrap();
            }
            let batsat = solve_with_rustsat_batsat(&f).unwrap();
            // Drive the solver with the EMA restart schedule enabled, through
            // the production policy surface.
            let mut sink = VecProofSink::new();
            let mut cdcl = Cdcl::new(&f, &mut sink);
            cdcl.set_policies(&SearchPolicies::ema_restart());
            assert!(
                cdcl.use_ema_restart,
                "`SearchPolicies::ema_restart` must actually select the EMA rule"
            );
            let outcome = cdcl.solve(None, DEFAULT_PROOF_SAT_CONFLICT_LIMIT);
            match (outcome, batsat) {
                (StreamingProofOutcome::Sat(model), SatResult::Sat(_)) => {
                    assert!(model.satisfies(&f).unwrap(), "EMA sat model must satisfy");
                }
                (StreamingProofOutcome::Unsat, SatResult::Unsat(_)) => {
                    assert_eq!(
                        check_drat(&f, &sink.into_steps()),
                        Ok(true),
                        "EMA unsat must DRAT-check"
                    );
                }
                (native, other) => {
                    panic!("DISAGREE (EMA restarts): native={native:?} batsat={other:?}");
                }
            }
        }
    }

    /// Blocking-literal BCP is a pure propagation optimization: it must NOT
    /// change any verdict. This battery re-affirms that — over a fresh seed of
    /// many random CNFs the blocking-literal core agrees with `BatSat` on every
    /// instance (`DISAGREE = 0`), every `sat` model satisfies, and every `unsat`
    /// proof (derived via the new `Watch`/blocker propagate) DRAT-checks. A
    /// blocker is a performance hint only; the implications and conflicts derived
    /// are identical to the plain two-watched scheme.
    #[test]
    #[cfg(feature = "batsat-reference")]
    fn blocking_literal_bcp_preserves_verdicts_disagree_zero() {
        let mut state = 0xb10c_11ad_5a7b_eef0u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let below = |n: &mut dyn FnMut() -> u64, bound: u64| usize::try_from(n() % bound).unwrap();
        for _ in 0..300 {
            let vars = 3 + below(&mut next, 8); // 3..=10 variables
            let clause_count = 4 + below(&mut next, 28);
            let mut f = CnfFormula::new(vars);
            let vars_bound = u64::try_from(vars).unwrap();
            for _ in 0..clause_count {
                let width = 1 + below(&mut next, 4); // 1..=4 literals (varied widths)
                let mut lits = Vec::new();
                for _ in 0..width {
                    let v = i64::try_from(next() % vars_bound).unwrap() + 1;
                    let signed = if next() & 1 == 0 { v } else { -v };
                    lits.push(lit(signed));
                }
                f.add_clause(CnfClause::new(lits)).unwrap();
            }
            let batsat = solve_with_rustsat_batsat(&f).unwrap();
            match (solve_with_drat_proof(&f), batsat) {
                (ProofSolveOutcome::Sat(model), SatResult::Sat(_)) => {
                    assert!(
                        model.satisfies(&f).unwrap(),
                        "native sat model must satisfy"
                    );
                }
                (ProofSolveOutcome::Unsat(proof), SatResult::Unsat(_)) => {
                    assert_eq!(
                        check_drat(&f, &proof),
                        Ok(true),
                        "native unsat must DRAT-check"
                    );
                }
                (native, other) => {
                    panic!("DISAGREE (blocking-literal BCP): native={native:?} batsat={other:?}");
                }
            }
        }
    }

    /// Builds an unsatisfiable pigeonhole formula: `pigeons` pigeons into
    /// `pigeons - 1` holes. PHP is exponentially hard for resolution, so larger
    /// instances generate many conflicts/learned clauses — enough to drive
    /// `reduce_db` at least once with the test-scaled budget.
    fn pigeonhole(pigeons: i64) -> CnfFormula {
        let holes = pigeons - 1;
        let v = |p: i64, h: i64| (p - 1) * holes + h; // var id, 1-based
        let nvars = usize::try_from(pigeons * holes).unwrap();
        let mut clauses: Vec<Vec<i64>> = Vec::new();
        for p in 1..=pigeons {
            clauses.push((1..=holes).map(|h| v(p, h)).collect());
        }
        for h in 1..=holes {
            for p1 in 1..=pigeons {
                for p2 in (p1 + 1)..=pigeons {
                    clauses.push(vec![-v(p1, h), -v(p2, h)]);
                }
            }
        }
        let refs: Vec<&[i64]> = clauses.iter().map(Vec::as_slice).collect();
        formula(nvars, &refs)
    }

    impl<S: DratSink> Cdcl<'_, S> {
        /// Reference branching rule: the exact O(n) linear scan the order heap
        /// replaces — the unassigned variable of highest activity, ties to the
        /// lowest index. Used only by trajectory-identity tests to confirm the
        /// heap returns the same variable as the scan.
        fn pick_branch_linear(&self) -> Option<usize> {
            let mut best: Option<usize> = None;
            for v in 0..self.assign.len() {
                if !self.branchable[v] || self.assign[v].is_some() {
                    continue;
                }
                match best {
                    None => best = Some(v),
                    Some(b) if self.activity[v] > self.activity[b] => best = Some(v),
                    _ => {}
                }
            }
            best
        }

        /// Asserts the order-heap invariants hold: every unassigned variable is in
        /// the heap, `heap_pos` is a consistent inverse of `heap`, and the heap
        /// property (`heap_before(parent, child)`) holds at every node.
        fn assert_heap_invariants(&self) {
            for (i, &v) in self.heap.iter().enumerate() {
                assert_eq!(self.heap_pos[v], i, "heap_pos must invert heap");
                if i > 0 {
                    let parent = self.heap[(i - 1) / 2];
                    assert!(
                        !self.heap_before(v, parent),
                        "heap property violated at {i}: {v} before parent {parent}"
                    );
                }
            }
            for v in 0..self.assign.len() {
                if self.branchable[v] && self.assign[v].is_none() {
                    assert!(
                        self.heap_contains(v),
                        "every unassigned variable must be in the heap: {v}"
                    );
                } else if !self.branchable[v] {
                    assert!(!self.heap_contains(v), "unused variable entered heap: {v}");
                }
            }
        }
    }

    #[test]
    fn unused_low_variables_do_not_delay_sparse_high_projection() {
        let f = formula(
            200_000,
            &[
                &[199_999, 200_000],
                &[199_999, -200_000],
                &[-199_999, 200_000],
                &[-199_999, -200_000],
            ],
        );
        let mut sink = VecProofSink::new();
        let cdcl = Cdcl::new(&f, &mut sink);
        assert_eq!(cdcl.heap, vec![199_998, 199_999]);
        assert_eq!(cdcl.branchable.iter().filter(|&&active| active).count(), 2);
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&f) else {
            panic!("four Boolean cells exhaust the two active variables");
        };
        assert_eq!(proof.len(), 2);
        assert_eq!(crate::check_drat(&f, &proof), Ok(true));
    }

    /// The order heap returns exactly the variable the O(n) linear scan would,
    /// under randomized bump / pop / backtrack stress, and its structural
    /// invariants hold throughout. This is the trajectory-identity guarantee at
    /// the branching-decision level: if the heap ever picked a different variable
    /// than the scan, the search trajectory would diverge.
    #[test]
    fn order_heap_matches_linear_scan_under_stress() {
        let mut state = 0x51ce_d00d_face_0042u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        // A dummy unit formula gives us a fully-initialized Cdcl with n vars all
        // in the heap; we then drive bump/pick/backtrack by hand.
        let n = 64usize;
        let n_signed = i64::try_from(n).unwrap();
        let n_bound = u64::try_from(n).unwrap();
        let mut clauses: Vec<Vec<i64>> = vec![vec![1]];
        clauses.extend((1..=n_signed).map(|v| vec![v, -v])); // tautologies, harmless
        let refs: Vec<&[i64]> = clauses.iter().map(Vec::as_slice).collect();
        let f = formula(n, &refs);
        let mut sink = VecProofSink::new();
        let mut cdcl = Cdcl::new(&f, &mut sink);
        cdcl.assert_heap_invariants();

        for _ in 0..20_000 {
            match next() % 3 {
                // Bump a random variable (raises its activity → sift-up).
                0 => {
                    let v = usize::try_from(next() % n_bound).unwrap();
                    cdcl.bump_var(v);
                    cdcl.decay();
                    cdcl.assert_heap_invariants();
                }
                // Pick the best variable and "decide" it (assign + push a level),
                // first checking the heap agrees with the linear scan.
                1 => {
                    let expected = cdcl.pick_branch_linear();
                    let got = cdcl.pick_branch();
                    assert_eq!(got, expected, "heap pick must match linear scan");
                    if let Some(v) = got {
                        cdcl.trail_lim.push(cdcl.trail.len());
                        let pos = CnfLit::positive(CnfVar::new(v).unwrap());
                        cdcl.enqueue(pos, Reason::DECISION);
                    }
                    cdcl.assert_heap_invariants();
                }
                // Backtrack to a random earlier level (unassign → re-insert).
                _ => {
                    if !cdcl.trail_lim.is_empty() {
                        let lvl =
                            usize::try_from(next() % (cdcl.trail_lim.len() as u64 + 1)).unwrap();
                        cdcl.backtrack_to(lvl);
                    }
                    cdcl.assert_heap_invariants();
                }
            }
        }
    }

    /// Determinism of the heap-driven core: the same formula yields a
    /// byte-identical proof across independent runs (the heap is fully
    /// deterministic — fixed insertion order at init, total `heap_before`
    /// ordering, no hashmap iteration). Uses a reducing pigeonhole instance so
    /// the run exercises bump, pop, backtrack, restart, and `reduce_db`.
    #[test]
    fn heap_driven_solve_is_byte_identical_across_runs() {
        let f = pigeonhole(8);
        let a = solve_with_drat_proof(&f);
        let b = solve_with_drat_proof(&f);
        assert_eq!(a, b, "heap-driven run must be byte-identical across runs");
        match &a {
            ProofSolveOutcome::Unsat(proof) => {
                assert_eq!(check_drat(&f, proof), Ok(true), "proof must DRAT-check");
            }
            other => panic!("expected unsat, got {other:?}"),
        }
    }

    /// Counts the clause-deletion (`d`) steps in a proof.
    fn deletion_count(proof: &[crate::DratStep]) -> usize {
        proof
            .iter()
            .filter(|s| matches!(s, crate::DratStep::Delete(_)))
            .count()
    }

    /// A pigeonhole instance large enough to trigger at least one `reduce_db`
    /// produces a proof containing DRAT deletion (`d`) lines, and that proof —
    /// WITH the deletions — still passes the independent checker and derives the
    /// empty clause. This is the core soundness gate for clause-DB reduction.
    #[test]
    fn reduce_db_emits_deletions_and_proof_still_checks() {
        // PHP(8→7): 56 vars, ~196 clauses; resolution-hard, so the core learns
        // far more than REDUCE_FIRST clauses and reduces at least once.
        let f = pigeonhole(8);
        match solve_with_drat_proof(&f) {
            ProofSolveOutcome::Unsat(proof) => {
                assert!(
                    deletion_count(&proof) > 0,
                    "a reducing run must emit DRAT deletions; got none"
                );
                assert_eq!(
                    check_drat(&f, &proof),
                    Ok(true),
                    "proof with deletion lines must DRAT-check and derive the empty clause"
                );
            }
            other => panic!("expected unsat, got {other:?}"),
        }
    }

    /// R9: the binary tag rides in bit 0 of the clause reference, so it must
    /// survive a reference that uses every other bit. A tag packed into the
    /// wrong end, or a `clause()` that forgets to shift, passes every
    /// small-formula test in this file and corrupts a large one.
    #[test]
    fn the_binary_tag_round_trips_beside_the_largest_clause_reference() {
        let biggest: CRef = usize::MAX >> 1;
        for cid in [0, 1, 2, 1_000_000, biggest] {
            for binary in [false, true] {
                let w = Watch::new(cid, lit(3), binary);
                assert_eq!(w.clause(), cid, "clause id must survive the tag");
                assert_eq!(w.is_binary(), binary, "tag must survive the clause id");
                assert_eq!(w.blocker, lit(3));
            }
        }
        // The packing is what keeps the tick unit fixed; see `WATCH_BYTES`.
        assert_eq!(size_of::<Watch>(), WATCH_BYTES_ON_TARGET);
    }

    /// R9, the property the change exists for: on a formula whose every clause
    /// is binary, propagation must never dereference the clause arena.
    ///
    /// `clause_visits` counts exactly the watches that had to read the clause,
    /// so `== 0` here is the claim itself and not a proxy for it. The two
    /// positive assertions are what stop it being vacuous: without them a build
    /// that visited no watches at all would pass.
    #[test]
    fn an_all_binary_formula_is_solved_without_one_arena_dereference() {
        // 2-SAT, unsatisfiable, and not by unit propagation alone: there are no
        // unit clauses, so the solver must decide, and either polarity of `x1`
        // falsifies one of the two pairs below. The chained implications give
        // the propagator real watch traffic to run through.
        let f = formula(
            8,
            &[
                &[1, 2],
                &[1, -2],
                &[-1, 3],
                &[-1, -3],
                &[-4, 5],
                &[-5, 6],
                &[-6, 7],
                &[-7, 8],
                &[4, -8],
                &[2, 4],
            ],
        );
        let mut sink = VecProofSink::new();
        let (outcome, c) =
            solve_with_drat_proof_counted(&f, None, DEFAULT_PROOF_SAT_CONFLICT_LIMIT, &mut sink);
        assert!(
            matches!(outcome, StreamingProofOutcome::Unsat),
            "the fixture must be unsat, got {outcome:?}"
        );
        assert_eq!(
            check_drat(&f, &sink.into_steps()),
            Ok(true),
            "the proof of an all-binary refutation must still check"
        );
        assert!(
            c.watch_visits > 0,
            "the fixture must actually propagate, or the claim below is vacuous"
        );
        assert!(
            c.binary_arena_derefs_avoided > 0,
            "the binary fast path must fire, or the claim below is vacuous"
        );
        assert_eq!(
            c.binary_watch_visits, c.watch_visits,
            "every clause here is binary, so every watch visit must be tagged binary"
        );
        assert_eq!(
            c.clause_visits, 0,
            "a binary clause must be decided from its watch alone; {} arena \
             dereferences means the fast path is not taken",
            c.clause_visits
        );
    }

    /// R9's cost: a binary clause's arena slots are no longer permuted, so the
    /// implied literal of a binary reason can sit at slot 1. `is_locked` reads
    /// slot 0 first, so a reader that stops there reports a locked clause as
    /// unlocked — and `reduce_db` would then be free to delete the reason for a
    /// currently-assigned literal.
    ///
    /// The two assertions are ordered deliberately: the first pins the *broken*
    /// invariant, so the test cannot quietly become a tautology if some future
    /// change restores the swap; the second is the behaviour that has to
    /// survive it.
    #[test]
    fn a_binary_clause_is_locked_through_the_literal_at_either_slot() {
        let f = formula(2, &[&[1, 2]]);
        let mut sink = VecProofSink::new();
        let mut cdcl = Cdcl::new(&f, &mut sink);
        let cid: CRef = 0;
        // Decide ~x1 at level 1; the only clause then implies x2.
        cdcl.push_level();
        cdcl.enqueue(lit(-1), Reason::DECISION);
        assert!(cdcl.propagate().is_none(), "no conflict is possible here");
        let implied = lit(2).var().index();
        assert_eq!(
            cdcl.reason[implied].as_clause(),
            Some(cid),
            "setup: x2 must be implied by the binary clause"
        );
        assert_eq!(
            cdcl.lit_at(cid, 0),
            lit(1),
            "the implied literal must NOT have been swapped to slot 0 — that is \
             the invariant this change gives up, and the point of the test"
        );
        assert!(
            cdcl.is_locked(cid),
            "a binary clause that is the reason for an assigned literal is locked \
             wherever that literal sits"
        );
    }

    /// R10: the two reduce-round watch sweeps must agree on the watch *set* and
    /// may differ only in per-list order — which is exactly what makes the
    /// choice visible to the search, and why it is a policy knob rather than a
    /// replacement.
    #[test]
    fn the_two_reduce_sweeps_agree_on_the_watch_set_and_differ_only_in_order() {
        let f = formula(5, &[&[1, 2, 3], &[-1, 2, 4], &[1, -2, 5], &[2, 3, -4]]);
        let mut sink = VecProofSink::new();
        let mut cdcl = Cdcl::new(&f, &mut sink);
        let code = lit_code(lit(2));
        let ids = |c: &Cdcl<'_, &mut VecProofSink>| -> Vec<CRef> {
            c.watches[code].iter().map(|w| w.clause()).collect()
        };
        assert!(
            ids(&cdcl).len() >= 3,
            "setup: literal 2 must be watched by several clauses"
        );
        // Stand in for what propagation does over a run: a relocated watch is
        // appended to its new list, so a list is not in clause-id order.
        cdcl.watches[code].rotate_left(1);
        let rotated = ids(&cdcl);

        cdcl.prune_watches();
        assert_eq!(
            ids(&cdcl),
            rotated,
            "the in-place sweep must preserve each list's order exactly"
        );

        cdcl.rebuild_watches();
        let rebuilt = ids(&cdcl);
        assert_ne!(
            rebuilt, rotated,
            "the rebuild sweep must put the list back into clause-id order; if it \
             did not, the two sweeps would be the same search and the A/B arm \
             would measure nothing"
        );
        let mut a = rotated;
        let mut b = rebuilt;
        a.sort_unstable();
        b.sort_unstable();
        assert_eq!(a, b, "the two sweeps must keep the same watch SET");

        // And the part that makes either sweep correct at all: a tombstoned
        // clause must lose every watch under both.
        for sweep in [WatchSweep::InPlace, WatchSweep::Rebuild] {
            let mut sink = VecProofSink::new();
            let mut cdcl = Cdcl::new(&f, &mut sink);
            cdcl.db_policy.watch_sweep = sweep;
            cdcl.deleted[1] = true;
            cdcl.sweep_watches();
            assert!(
                cdcl.watches.iter().flatten().all(|w| w.clause() != 1),
                "{sweep:?} left a watch on a tombstoned clause"
            );
            assert!(
                cdcl.watches.iter().flatten().any(|w| w.clause() == 0),
                "{sweep:?} dropped a live clause's watches"
            );
        }
    }

    /// R10: the reduce scan may only skip clause ids that the scan's own guard
    /// would have skipped anyway. Skipping a live learned clause would silently
    /// make it immortal, which no counter in this file would notice.
    #[test]
    fn the_reduce_scan_start_never_passes_a_live_learned_clause() {
        let f = formula(4, &[&[1, 2], &[3, 4]]);
        let mut sink = VecProofSink::new();
        let mut cdcl = Cdcl::new(&f, &mut sink);
        // Two input clauses (never candidates) then three learned ones.
        for lits in [
            vec![lit(1), lit(3)],
            vec![lit(2), lit(4)],
            vec![lit(1), lit(4)],
        ] {
            let cid = cdcl.alloc_clause(&lits);
            cdcl.lbd.push(2);
            cdcl.cla_activity.push(0.0);
            cdcl.used.push(0);
            cdcl.deleted.push(false);
            cdcl.learned.push(true);
            assert_eq!(cid + 1, cdcl.headers.len());
        }
        cdcl.deleted[3] = true;

        cdcl.advance_reduce_scan_start();
        assert_eq!(
            cdcl.reduce_scan_start, 2,
            "the scan must skip the two input clauses and stop at the first live \
             learned one"
        );
        // Tombstone that one too: the start may then move past it AND past the
        // already-dead clause behind it, but not past the live clause at 4.
        cdcl.deleted[2] = true;
        cdcl.advance_reduce_scan_start();
        assert_eq!(cdcl.reduce_scan_start, 4);
        assert!(
            (cdcl.reduce_scan_start..cdcl.headers.len())
                .any(|cid| cdcl.learned[cid] && !cdcl.deleted[cid]),
            "the surviving learned clause must still be inside the scanned range"
        );
    }

    /// Determinism with reduction active: the same reducing instance produces a
    /// byte-identical proof (same learned clauses, same deletions, same order)
    /// across runs. The reduce trigger is by deterministic conflict/learned
    /// count, the sort is total (tie-broken by clause id), and no hashmap
    /// iteration leaks into the output.
    #[test]
    fn reduce_db_is_deterministic() {
        let f = pigeonhole(8);
        let a = solve_with_drat_proof(&f);
        let b = solve_with_drat_proof(&f);
        assert_eq!(a, b, "reducing run must be deterministic");
        if let ProofSolveOutcome::Unsat(proof) = &a {
            assert!(deletion_count(proof) > 0, "expected reduction to fire");
        } else {
            panic!("expected unsat");
        }
    }

    /// A clause currently serving as the reason (antecedent) for an assigned
    /// literal is LOCKED and must never be deleted by `reduce_db`. We construct a
    /// state with a learned, non-glue, locked clause and assert `reduce_db`
    /// leaves it live.
    #[test]
    fn reduce_db_never_deletes_a_locked_clause() {
        // Decisions assign a=T, b=T, c=T at three distinct levels; the learned
        // clause (¬a ∨ ¬b ∨ ¬c ∨ d) over those gives LBD 4 (> GLUE_LBD) and is
        // the reason for d, so it is both deletable-by-shape and locked.
        let f = formula(4, &[&[1]]); // 4 vars; dummy clause
        let mut sink = VecProofSink::new();
        let mut cdcl = Cdcl::new(&f, &mut sink);
        // Manually drive three decision levels.
        let dlit = |sign: i64| lit(sign);
        cdcl.trail_lim.push(cdcl.trail.len());
        cdcl.enqueue(dlit(1), Reason::DECISION); // a@1
        cdcl.trail_lim.push(cdcl.trail.len());
        cdcl.enqueue(dlit(2), Reason::DECISION); // b@2
        cdcl.trail_lim.push(cdcl.trail.len());
        cdcl.enqueue(dlit(3), Reason::DECISION); // c@3
        // Add a learned clause that implies d, watched on its first two lits.
        let learned = vec![lit(4), lit(-1), lit(-2), lit(-3)]; // d ∨ ¬a ∨ ¬b ∨ ¬c
        let cid = cdcl.alloc_clause(&learned);
        cdcl.watches[lit_code(learned[0])].push(Watch::new(cid, learned[1], learned.len() == 2));
        cdcl.watches[lit_code(learned[1])].push(Watch::new(cid, learned[0], learned.len() == 2));
        cdcl.lbd.push(4); // distinct levels among ¬a,¬b,¬c,d (d will be @3)
        cdcl.cla_activity.push(0.0);
        cdcl.used.push(0); // cold: only the LOCK may save it
        cdcl.deleted.push(false);
        cdcl.learned.push(true); // parallel to `headers`; `reduce_db` reads it
        cdcl.learned_live += 1;
        cdcl.enqueue(dlit(4), Reason::clause(cid)); // d@3, reason = cid → cid is LOCKED
        assert!(cdcl.is_locked(cid), "setup: the clause must be locked");
        // Force reduce_db to run regardless of budget.
        cdcl.reduce_db().expect("the vec sink cannot fail");
        assert!(
            !cdcl.deleted[cid],
            "reduce_db must never delete a locked reason clause"
        );
    }

    /// The stamped LBD must agree with the definition it replaced -- the number
    /// of distinct decision levels among a clause's literals -- on every input,
    /// not merely on the ones the search happens to produce.
    ///
    /// The old implementation (collect levels, sort, dedup, count) is written
    /// out here as the oracle rather than referenced, because the point is to
    /// check the new code against the DEFINITION and not against itself.
    #[test]
    fn stamped_lbd_matches_the_sorted_dedup_definition() {
        let f = formula(16, &[&[1]]);
        let mut sink = VecProofSink::new();
        let mut cdcl = Cdcl::new(&f, &mut sink);
        // A deterministic spread of level patterns: all-distinct, all-equal,
        // repeats, level zero, and the maximum level.
        let patterns: &[&[usize]] = &[
            &[0],
            &[3, 3, 3],
            &[1, 2, 3, 4],
            &[4, 1, 4, 1, 4],
            &[0, 0, 7, 7, 2],
            &[15, 15, 15, 15, 15, 15, 15, 15],
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
        ];
        for pattern in patterns {
            let lits: Vec<CnfLit> = (0..pattern.len())
                .map(|i| CnfLit::positive(CnfVar::new(i % 16).unwrap()))
                .collect();
            // Levels are written after the literals are built, so a repeated
            // variable index takes the LAST assignment -- which is exactly what
            // the oracle below reads too.
            for (i, l) in lits.iter().enumerate() {
                cdcl.level[l.var().index()] = pattern[i];
            }
            let mut oracle: Vec<usize> = lits.iter().map(|l| cdcl.level[l.var().index()]).collect();
            oracle.sort_unstable();
            oracle.dedup();
            assert_eq!(
                cdcl.compute_lbd(&lits),
                oracle.len(),
                "stamped LBD disagreed with sorted-dedup on levels {pattern:?}"
            );
        }
        // And back-to-back calls must not leak state between clauses: a second
        // call on a one-level clause must not inherit the first's stamps.
        cdcl.level[0] = 5;
        let single = vec![CnfLit::positive(CnfVar::new(0).unwrap())];
        assert_eq!(cdcl.compute_lbd(&single), 1);
        assert_eq!(
            cdcl.compute_lbd(&single),
            1,
            "stamp generation did not advance"
        );
    }

    /// The keep rule must be *consulted*, not merely present. Under the tier
    /// policy a glue-2 clause that has gone cold is deletable; under the legacy
    /// rule it is immortal. Constructing exactly that clause and running one
    /// reduce round with each policy is the discriminating fixture: a
    /// `reduce_db` that ignored `db_policy` would give the same answer twice.
    #[test]
    fn a_cold_low_glue_clause_is_deletable_under_tiers_and_not_under_legacy() {
        use crate::clause_db_policy::ClauseDbPolicy;

        for (policy, expect_deleted) in [
            (ClauseDbPolicy::tiered(), true),
            (ClauseDbPolicy::legacy(), false),
        ] {
            let f = formula(8, &[&[1]]);
            let mut sink = VecProofSink::new();
            let mut cdcl = Cdcl::new(&f, &mut sink);
            cdcl.db_policy = policy;
            // Three learned clauses, all glue 2, all length 3, none locked and
            // none the reason for anything (the trail is empty).
            let mut ids = Vec::new();
            for base in [2i64, 3, 4] {
                let learned = vec![lit(base), lit(base + 1), lit(base + 2)];
                let cid = cdcl.alloc_clause(&learned);
                cdcl.lbd.push(2);
                cdcl.cla_activity.push(0.0);
                cdcl.used.push(0); // cold: not resolved since the last round
                cdcl.deleted.push(false);
                cdcl.learned.push(true);
                cdcl.learned_live += 1;
                ids.push(cid);
            }
            cdcl.reduce_db().expect("the vec sink cannot fail");
            let deleted = ids.iter().filter(|&&cid| cdcl.deleted[cid]).count();
            assert_eq!(
                deleted > 0,
                expect_deleted,
                "cold glue-2 clauses: deleted {deleted} of 3, expected \
                 deleted>0 == {expect_deleted}"
            );
        }
    }

    /// The other half of the tier rule: a low-glue clause that WAS resolved
    /// since the previous round survives, on the same fixture that deletes the
    /// cold one. Without this, the test above would also pass a policy that
    /// simply deleted everything.
    #[test]
    fn a_recently_used_tier1_clause_survives_the_round_that_deletes_a_cold_one() {
        let f = formula(8, &[&[1]]);
        let mut sink = VecProofSink::new();
        let mut cdcl = Cdcl::new(&f, &mut sink);
        let mut ids = Vec::new();
        for (i, base) in [2i64, 3, 4, 5].into_iter().enumerate() {
            let learned = vec![lit(base), lit(base + 1), lit(base + 2)];
            let cid = cdcl.alloc_clause(&learned);
            cdcl.lbd.push(2);
            cdcl.cla_activity.push(0.0);
            // Alternate hot and cold.
            cdcl.used.push(if i % 2 == 0 {
                crate::clause_db_policy::MAX_USED
            } else {
                0
            });
            cdcl.deleted.push(false);
            cdcl.learned.push(true);
            cdcl.learned_live += 1;
            ids.push(cid);
        }
        cdcl.reduce_db().expect("the vec sink cannot fail");
        for (i, &cid) in ids.iter().enumerate() {
            if i % 2 == 0 {
                assert!(
                    !cdcl.deleted[cid],
                    "a tier1 clause resolved since the last round must survive"
                );
            }
        }
        assert!(
            ids.iter().any(|&cid| cdcl.deleted[cid]),
            "the round must delete the cold clauses; deleting nothing would make \
             the assertion above vacuous"
        );
    }

    /// Every reduce round ages every live learned clause. Without the
    /// decrement, `used` would stay at its maximum forever and the tier rule
    /// would degenerate into "keep everything ever resolved".
    #[test]
    fn a_reduce_round_ages_every_live_learned_clause() {
        let f = formula(8, &[&[1]]);
        let mut sink = VecProofSink::new();
        let mut cdcl = Cdcl::new(&f, &mut sink);
        let learned = vec![lit(2), lit(3), lit(4)];
        let cid = cdcl.alloc_clause(&learned);
        cdcl.lbd.push(2);
        cdcl.cla_activity.push(0.0);
        cdcl.used.push(crate::clause_db_policy::MAX_USED);
        cdcl.deleted.push(false);
        cdcl.learned.push(true);
        cdcl.learned_live += 1;
        cdcl.reduce_db().expect("the vec sink cannot fail");
        assert!(!cdcl.deleted[cid], "setup: this clause must survive");
        assert_eq!(
            cdcl.used[cid],
            crate::clause_db_policy::MAX_USED - 1,
            "a reduce round must decrement the lifetime counter"
        );
    }

    /// The dynamic boundaries must actually move on a real search, or R2 is
    /// implemented but inert. PHP(8) resolves through enough clauses that the
    /// used-glue histogram is well populated, and its glue profile is not 2/6.
    #[test]
    fn tier_boundaries_are_recomputed_and_leave_the_fallback_on_a_real_search() {
        let f = pigeonhole(8);
        let mut sink = VecProofSink::new();
        let (outcome, c) =
            solve_with_drat_proof_counted(&f, None, DEFAULT_PROOF_SAT_CONFLICT_LIMIT, &mut sink);
        assert!(matches!(outcome, StreamingProofOutcome::Unsat));
        assert!(
            c.tier_recomputes > 0,
            "the tier estimator never recomputed; the schedule is inert"
        );
        assert!(
            c.clause_used_marks > 0,
            "no clause was ever marked used; the histogram is empty by construction"
        );
        // The boundaries must be a *measurement*, not the fallback echoed back.
        // An estimator that never read its histogram would report 2/6 forever,
        // so a mean that differs from the fallback is the discriminating check.
        #[allow(clippy::cast_precision_loss)]
        let mean_tier2 = c.tier2_limit_sum as f64 / c.tier_recomputes as f64;
        assert!(
            (c.tier1_limit_last, c.tier2_limit_last) != (2, 6) || (mean_tier2 - 6.0).abs() > 1e-9,
            "tier boundaries never left the 2/6 fallback over {} recomputations",
            c.tier_recomputes
        );
        assert!(
            c.tier2_limit_last >= c.tier1_limit_last,
            "tier2 ({}) must never fall below tier1 ({})",
            c.tier2_limit_last,
            c.tier1_limit_last
        );
    }

    /// Reduce-round accounting must partition the population it examined: every
    /// live learned clause is locked, too short, kept by a tier rule, or a
    /// candidate. A counter set that did not add up would make every tuning
    /// conclusion drawn from it unfalsifiable.
    #[test]
    fn reduce_counters_partition_the_clauses_they_examined() {
        let f = pigeonhole(8);
        let mut sink = VecProofSink::new();
        let (_, c) =
            solve_with_drat_proof_counted(&f, None, DEFAULT_PROOF_SAT_CONFLICT_LIMIT, &mut sink);
        assert!(
            c.reductions > 0,
            "no reduce round ran; the test measures nothing"
        );
        let by_tier = c.reduce_tier1_seen + c.reduce_tier2_seen + c.reduce_tier3_seen;
        let by_outcome = c.reduce_locked
            + c.reduce_too_short
            + c.reduce_kept_tier1
            + c.reduce_kept_tier2
            + c.reduce_candidates;
        assert_eq!(
            by_tier, by_outcome,
            "every examined clause must be counted exactly once by tier and \
             exactly once by outcome ({by_tier} by tier vs {by_outcome} by outcome)"
        );
        assert!(
            c.reduce_deleted > 0 && c.reduce_deleted <= c.reduce_candidates,
            "deleted {} of {} candidates",
            c.reduce_deleted,
            c.reduce_candidates
        );
    }

    /// The policy decides which clauses are forgotten; it must not decide the
    /// verdict, and it must not break the proof. Both policies, over
    /// resolution-hard instances, must return `unsat` with a DRAT proof that
    /// the independent checker accepts *including its deletion lines*.
    #[test]
    fn both_clause_db_policies_are_sound_and_their_proofs_check() {
        use super::{SearchPolicies, solve_with_drat_proof_counted_with_policies};

        // PHP(6) is small enough that neither policy reduces at all; it is kept
        // in the sweep as a soundness case, but only the instances that
        // actually reduce can say anything about the clause database.
        let mut reducing_instances = 0;
        for pigeons in [6, 7, 8] {
            let f = pigeonhole(pigeons);
            let mut fingerprints = Vec::new();
            let mut deletions = Vec::new();
            for policies in [SearchPolicies::default(), SearchPolicies::legacy()] {
                let mut sink = VecProofSink::new();
                let (outcome, c) = solve_with_drat_proof_counted_with_policies(
                    &f,
                    None,
                    DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
                    &mut sink,
                    &policies,
                );
                assert!(
                    matches!(outcome, StreamingProofOutcome::Unsat),
                    "PHP({pigeons}) must be unsat under every policy, got {outcome:?}"
                );
                let proof = sink.into_steps();
                assert_eq!(
                    check_drat(&f, &proof),
                    Ok(true),
                    "PHP({pigeons}) proof must DRAT-check with its deletions"
                );
                deletions.push(deletion_count(&proof));
                fingerprints.push((c.conflicts, proof.len()));
            }
            if deletions.iter().all(|&d| d == 0) {
                continue;
            }
            reducing_instances += 1;
            // The two policies are genuinely different searches, not the same
            // one behind two names. If this ever holds, the A/B measurement it
            // exists to support is measuring nothing.
            assert_ne!(
                fingerprints[0], fingerprints[1],
                "PHP({pigeons}): the tier policy and the legacy policy produced \
                 identical (conflicts, proof length); the policy object is not \
                 reaching the search"
            );
        }
        assert!(
            reducing_instances > 0,
            "no instance in the sweep reduced, so nothing about the clause \
             database was tested"
        );
    }

    /// R6: the target high-water mark is a ratchet, and whether it releases is
    /// a policy choice. Under the pinned policy it never resets; under the
    /// rephase schedule it does, and the schedule fires.
    #[test]
    fn the_target_phase_ratchet_releases_only_under_a_rephase_schedule() {
        use super::{SearchPolicies, solve_with_drat_proof_counted_with_policies};

        let f = pigeonhole(8);
        let mut pinned_sink = VecProofSink::new();
        let (pinned_outcome, pinned) = solve_with_drat_proof_counted_with_policies(
            &f,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            &mut pinned_sink,
            &SearchPolicies::default(),
        );
        let mut scheduled_sink = VecProofSink::new();
        let (scheduled_outcome, scheduled) = solve_with_drat_proof_counted_with_policies(
            &f,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            &mut scheduled_sink,
            &SearchPolicies::scheduled_phase(),
        );

        assert!(matches!(pinned_outcome, StreamingProofOutcome::Unsat));
        assert!(matches!(scheduled_outcome, StreamingProofOutcome::Unsat));
        assert_eq!(
            check_drat(&f, &scheduled_sink.into_steps()),
            Ok(true),
            "the rephasing run's proof must still check"
        );
        assert_eq!(
            pinned.target_phase_resets, 0,
            "the pinned policy must never release the mark"
        );
        assert!(
            scheduled.rephases > 0,
            "the rephase schedule never fired over {} conflicts",
            scheduled.conflicts
        );
        assert_eq!(
            scheduled.target_phase_resets, scheduled.rephases,
            "every rephase releases the target mark"
        );
        // The measurable symptom of a pinned ratchet: the snapshot stops firing.
        // With a release it keeps firing, so the rate must be strictly larger.
        // Stated as a ratio because the two runs take different trajectories
        // and therefore analyse different numbers of conflicts.
        #[allow(clippy::cast_precision_loss)]
        let pinned_rate = pinned.target_phase_snapshots as f64 / pinned.conflicts.max(1) as f64;
        #[allow(clippy::cast_precision_loss)]
        let released_rate =
            scheduled.target_phase_snapshots as f64 / scheduled.conflicts.max(1) as f64;
        assert!(
            released_rate > pinned_rate,
            "releasing the ratchet did not increase the target-snapshot rate \
             ({released_rate} vs {pinned_rate}); the reset is not reaching the mark"
        );
    }

    /// Reduction stress: many random CNFs solved with reduction active. The
    /// native core and `BatSat` must never disagree, every native `sat` model
    /// must satisfy, and every native `unsat` proof — including its deletion
    /// lines — must DRAT-check. This is the completeness+soundness gate: no UNSAT
    /// is ever reported SAT or vice-versa even as the clause DB churns.
    #[test]
    #[cfg(feature = "batsat-reference")]
    fn reduce_db_stress_agrees_with_batsat_and_proof_checks() {
        // A spread of resolution-hard pigeonhole instances guarantees several
        // reductions; the random suite guarantees breadth.
        for pigeons in [6, 7, 8] {
            let f = pigeonhole(pigeons);
            let batsat = solve_with_rustsat_batsat(&f).unwrap();
            match (solve_with_drat_proof(&f), batsat) {
                (ProofSolveOutcome::Unsat(proof), SatResult::Unsat(_)) => {
                    assert_eq!(
                        check_drat(&f, &proof),
                        Ok(true),
                        "PHP({pigeons}) proof with deletions must DRAT-check"
                    );
                }
                (native, other) => {
                    panic!("DISAGREE on PHP({pigeons}): native={native:?} batsat={other:?}");
                }
            }
        }

        let mut state = 0xfeed_face_cafe_b0ddu64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let below = |n: &mut dyn FnMut() -> u64, bound: u64| usize::try_from(n() % bound).unwrap();
        for _ in 0..200 {
            let vars = 5 + below(&mut next, 8); // 5..=12 variables
            let clause_count = 8 + below(&mut next, 30);
            let mut f = CnfFormula::new(vars);
            let vars_bound = u64::try_from(vars).unwrap();
            for _ in 0..clause_count {
                let mut lits = Vec::new();
                for _ in 0..3 {
                    let v = i64::try_from(next() % vars_bound).unwrap() + 1;
                    let signed = if next() & 1 == 0 { v } else { -v };
                    lits.push(lit(signed));
                }
                f.add_clause(CnfClause::new(lits)).unwrap();
            }
            let batsat = solve_with_rustsat_batsat(&f).unwrap();
            match (solve_with_drat_proof(&f), batsat) {
                (ProofSolveOutcome::Sat(model), SatResult::Sat(_)) => {
                    assert!(
                        model.satisfies(&f).unwrap(),
                        "native sat model must satisfy"
                    );
                }
                (ProofSolveOutcome::Unsat(proof), SatResult::Unsat(_)) => {
                    assert_eq!(
                        check_drat(&f, &proof),
                        Ok(true),
                        "native unsat (with any deletions) must DRAT-check"
                    );
                }
                (native, other) => {
                    panic!("DISAGREE: native={native:?} batsat={other:?}");
                }
            }
        }
    }

    // ----------------------------------------------------------------------
    // Streaming proof emission (ADR-0381)
    // ----------------------------------------------------------------------

    /// A Rado-style colouring instance: is `[1, n]` `colours`-colourable with no
    /// monochromatic solution of `a(x − y) = b z`? Variable `(i, c)` (1-based
    /// DIMACS `(i - 1) * colours + c`) says "integer `i` has colour `c`";
    /// at-least-one-colour per integer, plus one clause per solution triple per
    /// colour. `(a, b) = (1, 1)` is the Schur equation `x = y + z`.
    ///
    /// This is the shape of the instances in the claim-ledger campaign
    /// (`docs/plan/claim-ledger-and-rado-frontier-2026-08-12.md`) that motivated
    /// streaming — a few hundred clauses here, enough to produce a proof with
    /// many steps and at least one clause-DB reduction on the harder settings.
    fn rado_colouring(n: i64, colours: i64, a: i64, b: i64) -> CnfFormula {
        let var = |i: i64, c: i64| (i - 1) * colours + c;
        let mut clauses: Vec<Vec<i64>> = Vec::new();
        for i in 1..=n {
            clauses.push((1..=colours).map(|c| var(i, c)).collect());
        }
        for x in 1..=n {
            for y in 1..=n {
                for z in 1..=n {
                    if a * (x - y) != b * z {
                        continue;
                    }
                    for c in 1..=colours {
                        // De-duplicate: a triple may repeat an integer (e.g.
                        // x = 2y with y = z), and a clause with a repeated
                        // literal would be watched twice on the same literal.
                        let mut lits = vec![-var(x, c), -var(y, c), -var(z, c)];
                        lits.sort_unstable();
                        lits.dedup();
                        clauses.push(lits);
                    }
                }
            }
        }
        let refs: Vec<&[i64]> = clauses.iter().map(Vec::as_slice).collect();
        formula(usize::try_from(n * colours).unwrap(), &refs)
    }

    /// The streaming entry emits, byte for byte, the proof the `Vec` route
    /// records — and reaches the same verdict as the non-streaming entry — on a
    /// spread of formulas (trivial contradictions, pigeonhole, a satisfiable
    /// instance, and Rado-style colouring instances of a few hundred clauses).
    ///
    /// This is the equivalence the design rests on: the sink is pure output, so
    /// the search trajectory cannot depend on it. If a future change let the sink
    /// influence the search, the emitted step sequences would diverge here.
    /// Satisfiable instances are covered too — a `sat` run still learns (and so
    /// emits) clauses, which the non-streaming entry simply discards.
    #[test]
    fn streaming_emission_matches_the_vec_proof_byte_for_byte() {
        let instances: Vec<(&str, CnfFormula)> = vec![
            ("unit contradiction", formula(1, &[&[1], &[-1]])),
            ("empty clause", formula(1, &[&[]])),
            (
                "full 2x2",
                formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]),
            ),
            ("satisfiable", formula(3, &[&[1, 2], &[-1, 3], &[-2, -3]])),
            ("php(6)", pigeonhole(6)),
            // Schur/Rado `x − y = z` with 3 colours: 13 is colourable, 14 is not
            // (287 clauses over 42 variables).
            ("rado 1,1 n=13 k=3", rado_colouring(13, 3, 1, 1)),
            ("rado 1,1 n=14 k=3", rado_colouring(14, 3, 1, 1)),
            // A second coefficient pair, so the battery is not one equation family.
            ("rado 2,3 n=12 k=2", rado_colouring(12, 2, 2, 3)),
        ];

        let mut unsat_with_proof = 0u32;
        let mut sat_with_steps = 0u32;
        for (name, f) in instances {
            let vec_outcome = solve_with_drat_proof(&f);

            // The same search, streamed to text …
            let mut text: Vec<u8> = Vec::new();
            let mut text_sink = TextProofSink::new(&mut text);
            let streamed = solve_with_drat_proof_streaming(
                &f,
                None,
                DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
                &mut text_sink,
            );
            text_sink.finish().expect("the vec writer cannot fail");
            // … and to a step vector, which `write_drat` then serializes. The two
            // must agree byte for byte whatever the verdict.
            let mut vec_sink = VecProofSink::new();
            let streamed_vec = solve_with_drat_proof_streaming(
                &f,
                None,
                DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
                &mut vec_sink,
            );
            let steps = vec_sink.into_steps();
            assert_eq!(streamed, streamed_vec, "{name}: sink must not steer search");
            assert_eq!(
                String::from_utf8(text).unwrap(),
                write_drat(&steps),
                "{name}: streamed text must be byte-identical to write_drat"
            );

            match (&vec_outcome, &streamed) {
                (ProofSolveOutcome::Unsat(proof), StreamingProofOutcome::Unsat) => {
                    assert_eq!(proof, &steps, "{name}: same steps, same order");
                    assert!(!proof.is_empty(), "{name}: an unsat proof has steps");
                    assert_eq!(
                        check_drat(&f, proof),
                        Ok(true),
                        "{name}: the proof must DRAT-check"
                    );
                    unsat_with_proof += 1;
                }
                (ProofSolveOutcome::Sat(model), StreamingProofOutcome::Sat(streamed_model)) => {
                    assert_eq!(model, streamed_model, "{name}: models must be identical");
                    assert!(model.satisfies(&f).unwrap(), "{name}: model must satisfy");
                    if !steps.is_empty() {
                        sat_with_steps += 1;
                    }
                }
                (a, b) => panic!("{name}: verdict mismatch: vec={a:?} streamed={b:?}"),
            }
        }
        assert!(
            unsat_with_proof >= 5,
            "the battery must actually exercise the proof path (got {unsat_with_proof} unsat runs)"
        );
        assert!(
            sat_with_steps >= 1,
            "the battery must include a sat run that emitted learned clauses"
        );
    }

    /// A streamed proof, checked back **without ever materializing it**: the text
    /// is read line by line by [`crate::DratTextReader`] and verified by
    /// [`crate::check_drat_streaming`]. This is the end-to-end bounded-memory
    /// route — produce to a writer, consume from a reader.
    #[test]
    fn streamed_text_proof_checks_back_through_the_streaming_checker() {
        let f = rado_colouring(14, 3, 1, 1);
        let mut text: Vec<u8> = Vec::new();
        let mut sink = TextProofSink::new(&mut text);
        let outcome =
            solve_with_drat_proof_streaming(&f, None, DEFAULT_PROOF_SAT_CONFLICT_LIMIT, &mut sink);
        sink.finish().unwrap();
        assert_eq!(outcome, StreamingProofOutcome::Unsat);
        assert!(!text.is_empty(), "an unsat run must emit proof text");

        let reader = crate::DratTextReader::new(std::io::BufReader::new(text.as_slice()));
        assert_eq!(
            crate::check_drat_streaming(&f, reader),
            Ok(true),
            "the streamed proof must verify straight from its text form"
        );
    }

    /// Determinism of the streamed route: two runs over the same formula produce
    /// identical bytes (the search is deterministic and the sink adds nothing).
    #[test]
    fn streamed_proof_bytes_are_identical_across_runs() {
        let f = pigeonhole(8);
        let run = || {
            let mut text: Vec<u8> = Vec::new();
            let mut sink = TextProofSink::new(&mut text);
            let outcome = solve_with_drat_proof_streaming(
                &f,
                None,
                DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
                &mut sink,
            );
            sink.finish().unwrap();
            (outcome, text)
        };
        let (first_outcome, first) = run();
        let (second_outcome, second) = run();
        assert_eq!(first_outcome, StreamingProofOutcome::Unsat);
        assert_eq!(second_outcome, first_outcome);
        assert!(!first.is_empty(), "expected a non-trivial proof");
        assert_eq!(first, second, "streamed runs must be byte-identical");
    }

    /// A sink that accepts a fixed number of steps and then fails — a disk
    /// filling up, or a pipe closing, mid-search.
    struct FailAfter {
        remaining: usize,
        calls: usize,
    }

    impl FailAfter {
        fn new(remaining: usize) -> Self {
            Self {
                remaining,
                calls: 0,
            }
        }

        fn tick(&mut self) -> Result<(), ProofSinkError> {
            self.calls += 1;
            if self.remaining == 0 {
                return Err(ProofSinkError::new(
                    std::io::ErrorKind::BrokenPipe,
                    "proof stream closed",
                ));
            }
            self.remaining -= 1;
            Ok(())
        }
    }

    impl DratSink for FailAfter {
        fn add_clause(&mut self, _lits: &[CnfLit]) -> Result<(), ProofSinkError> {
            self.tick()
        }

        fn delete_clause(&mut self, _lits: &[CnfLit]) -> Result<(), ProofSinkError> {
            self.tick()
        }
    }

    /// A sink that fails mid-search surfaces the error as an *undecided* outcome:
    /// no panic, and — critically — no `unsat` verdict, because a refutation
    /// whose proof could not be recorded is not a checked refutation.
    #[test]
    fn sink_failure_aborts_the_search_without_panicking() {
        // PHP(8) needs thousands of steps, so failing after 5 lands mid-search.
        let f = pigeonhole(8);
        let mut sink = FailAfter::new(5);
        let outcome =
            solve_with_drat_proof_streaming(&f, None, DEFAULT_PROOF_SAT_CONFLICT_LIMIT, &mut sink);
        match outcome {
            StreamingProofOutcome::SinkFailed(error) => {
                assert_eq!(error.kind(), std::io::ErrorKind::BrokenPipe);
                assert_eq!(error.message(), "proof stream closed");
            }
            other => panic!("expected SinkFailed, got {other:?}"),
        }
        assert_eq!(sink.calls, 6, "the search stops at the first refusal");

        // The same formula, with a sink that never fails, still decides unsat —
        // i.e. the failure above is the sink's, not the search's.
        let mut generous = FailAfter::new(usize::MAX);
        assert_eq!(
            solve_with_drat_proof_streaming(
                &f,
                None,
                DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
                &mut generous
            ),
            StreamingProofOutcome::Unsat
        );

        // A sink that fails on its very first step (the trivial-contradiction
        // path, before the conflict loop) is handled the same way.
        let mut immediate = FailAfter::new(0);
        assert!(matches!(
            solve_with_drat_proof_streaming(
                &formula(1, &[&[1], &[-1]]),
                None,
                DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
                &mut immediate
            ),
            StreamingProofOutcome::SinkFailed(_)
        ));
    }

    /// The streaming entry honours the resource limits exactly as the
    /// non-streaming one does — the budget is a search property, not a sink one.
    #[test]
    fn streaming_entry_honours_the_conflict_budget() {
        let f = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
        let mut sink = VecProofSink::new();
        assert_eq!(
            solve_with_drat_proof_streaming(&f, None, 0, &mut sink),
            StreamingProofOutcome::ResourceOut
        );
        assert_eq!(
            solve_with_drat_proof_with_limits(&f, None, 0),
            ProofSolveOutcome::ResourceOut
        );
    }

    /// The `Vec` sink reproduces the non-streaming proof exactly (same steps,
    /// same order), which is what lets the existing entry points delegate through
    /// it without any behavioral change.
    #[test]
    fn vec_sink_reproduces_the_non_streaming_proof() {
        for f in [pigeonhole(7), rado_colouring(14, 3, 1, 1)] {
            let ProofSolveOutcome::Unsat(expected) = solve_with_drat_proof(&f) else {
                panic!("fixture must be unsat");
            };
            let mut sink = VecProofSink::new();
            let outcome = solve_with_drat_proof_streaming(
                &f,
                None,
                DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
                &mut sink,
            );
            assert_eq!(outcome, StreamingProofOutcome::Unsat);
            assert_eq!(sink.into_steps(), expected, "step sequences must match");
        }
    }

    /// [`Reason`] must be **one word**, and never wider than the
    /// `Option<CRef>` it replaced -- the S6 memory requirement, asserted rather
    /// than assumed. It is read once per variable on every step of every
    /// conflict analysis and of recursive minimization, so a two-word reason
    /// would double that traffic across the whole solve.
    ///
    /// The comparison is the point: `Option<usize>` has no niche and is
    /// **16 bytes**, so packing the extra `Theory` case into 8 bytes makes the
    /// array *smaller* than before this change, not larger.
    #[test]
    fn reason_is_one_word_and_no_wider_than_the_option_it_replaced() {
        assert_eq!(
            size_of::<Reason>(),
            size_of::<usize>(),
            "Reason must be exactly one machine word"
        );
        assert!(
            size_of::<Reason>() <= size_of::<Option<usize>>(),
            "Reason ({}) must not be wider than the Option<CRef> ({}) it replaced",
            size_of::<Reason>(),
            size_of::<Option<usize>>()
        );
        // Per-variable memory is what the requirement is actually about.
        assert!(
            size_of::<Vec<Reason>>() == size_of::<Vec<Option<usize>>>()
                && size_of::<Reason>() * 1024 <= size_of::<Option<usize>>() * 1024,
            "a 1024-variable reason array must not grow"
        );
    }

    /// Every [`Reason`] case round-trips through the packing: the tag decides
    /// the case and the payload comes back bit-identical. A packed
    /// representation whose payload silently truncated would hand `explain` a
    /// handle the theory never issued, and the search would then be justified
    /// by the wrong clause.
    #[test]
    fn every_reason_case_round_trips_through_the_packing() {
        use super::{ExplanationId, ReasonKind};

        assert!(Reason::DECISION.is_decision());
        assert_eq!(Reason::DECISION.kind(), ReasonKind::Decision);
        assert_eq!(Reason::DECISION.as_clause(), None);
        assert_eq!(Reason::DECISION.as_theory(), None);

        // Clause 0 is a real CRef and must NOT be confused with a decision.
        for cref in [0usize, 1, 42, usize::from(u16::MAX), (1usize << 40) - 1] {
            let reason = Reason::clause(cref);
            assert!(
                !reason.is_decision(),
                "Clause({cref}) read back as a decision"
            );
            assert_eq!(reason.as_clause(), Some(cref));
            assert_eq!(reason.as_theory(), None);
            assert_eq!(reason.kind(), ReasonKind::Clause(cref));
        }

        for handle in [0u64, 1, 7, u64::from(u32::MAX), (1u64 << 40) - 1] {
            let reason = Reason::theory(ExplanationId(handle));
            assert!(
                !reason.is_decision(),
                "Theory({handle}) read back as a decision"
            );
            assert_eq!(reason.as_clause(), None);
            assert_eq!(reason.as_theory(), Some(ExplanationId(handle)));
            assert_eq!(reason.kind(), ReasonKind::Theory(ExplanationId(handle)));
        }

        // The three cases are pairwise distinct at the same payload -- the
        // property a single-sentinel encoding would lose.
        assert_ne!(Reason::clause(0), Reason::DECISION);
        assert_ne!(Reason::theory(ExplanationId(0)), Reason::DECISION);
        assert_ne!(Reason::clause(3), Reason::theory(ExplanationId(3)));
    }

    /// A handle too wide for the 62-bit payload is a hard error, not a silent
    /// truncation to a different handle.
    #[test]
    #[should_panic(expected = "exceeds the 62-bit Reason payload")]
    fn an_oversized_explanation_handle_panics_rather_than_truncating() {
        let _ = Reason::theory(super::ExplanationId(u64::MAX));
    }

    /// Theory-hook liveness (ADR-1701 slice 2 spike).
    ///
    /// The whole point of the spike measurement is that attaching a theory
    /// costs nothing when the theory is [`NullTheory`]. That claim is only
    /// meaningful if the hooks are actually *there* — a search that never calls
    /// them would measure zero cost and be worthless. These tests drive the
    /// same search with a theory that counts every call and with theories that
    /// answer non-trivially, so deleting a call site kills a test rather than
    /// silently improving the benchmark.
    mod theory_hooks {
        use std::cell::RefCell;
        use std::rc::Rc;

        use super::{
            Cdcl, DEFAULT_PROOF_SAT_CONFLICT_LIMIT, ProofSolveOutcome, StreamingProofOutcome,
            TheoryProofOutcome, VecProofSink, formula, pigeonhole, solve_with_drat_proof,
            solve_with_theory_and_drat_proof,
        };
        use crate::CnfLit;
        use crate::proof_sat::SearchOutcome;
        use crate::proof_sat::theory::{
            ExplanationId, FinalCheckOutcome, NativeTheory, PropagationQueue, TheoryExplanation,
        };

        /// How many times each hook was reached.
        #[derive(Debug, Default, PartialEq, Eq)]
        struct HookCounts {
            asserts: usize,
            pushes: usize,
            pops: usize,
            propagates: usize,
            final_checks: usize,
            new_atom_polls: usize,
        }

        /// A theory that answers exactly as [`NullTheory`] does but records
        /// every call. `HAS_THEORY` is the trait default (`true`), so this is
        /// also the arm that proves a *real* theory reaches the same code.
        struct CountingTheory(Rc<RefCell<HookCounts>>);

        impl NativeTheory for CountingTheory {
            fn assert(&mut self, _var: usize, _value: bool) -> Result<(), Vec<CnfLit>> {
                self.0.borrow_mut().asserts += 1;
                Ok(())
            }
            fn push(&mut self) {
                self.0.borrow_mut().pushes += 1;
            }
            fn pop(&mut self) {
                self.0.borrow_mut().pops += 1;
            }
            fn propagate_into(&mut self, _queue: &mut PropagationQueue) {
                self.0.borrow_mut().propagates += 1;
            }
            fn final_check(&mut self) -> FinalCheckOutcome {
                self.0.borrow_mut().final_checks += 1;
                FinalCheckOutcome::Sat
            }
            fn take_new_atoms(&mut self) -> usize {
                self.0.borrow_mut().new_atom_polls += 1;
                0
            }
        }

        /// Runs `formula` through the generic search with `theory` attached and
        /// returns the outcome together with the DRAT steps emitted.
        fn solve_with<T: NativeTheory>(
            f: &crate::CnfFormula,
            theory: T,
        ) -> (StreamingProofOutcome, Vec<crate::DratStep>) {
            let mut sink = VecProofSink::new();
            let outcome = Cdcl::new_with_theory(f, &mut sink, theory)
                .solve(None, DEFAULT_PROOF_SAT_CONFLICT_LIMIT);
            (outcome, sink.into_steps())
        }

        /// A satisfiable instance reaches assert, push, propagate, the
        /// new-atom poll, and **exactly one** `final_check` — the total
        /// assignment. If `theory_round` or the `final_check` call site were
        /// removed, the corresponding count would be zero and this fails.
        #[test]
        fn a_satisfiable_search_reaches_assert_push_propagate_and_final_check() {
            let counts = Rc::new(RefCell::new(HookCounts::default()));
            let f = formula(4, &[&[1, 2], &[-1, 3], &[-2, -3], &[3, 4]]);
            let (outcome, _) = solve_with(&f, CountingTheory(Rc::clone(&counts)));
            assert!(
                matches!(outcome, StreamingProofOutcome::Sat(_)),
                "fixture is satisfiable; got {outcome:?}"
            );
            let counts = counts.borrow();
            assert!(counts.asserts > 0, "assert hook never reached: {counts:?}");
            assert!(counts.pushes > 0, "push hook never reached: {counts:?}");
            assert!(
                counts.propagates > 0,
                "propagate_into hook never reached: {counts:?}"
            );
            assert!(
                counts.new_atom_polls > 0,
                "take_new_atoms hook never reached: {counts:?}"
            );
            assert_eq!(
                counts.final_checks, 1,
                "final_check runs exactly once, at the one total assignment: {counts:?}"
            );
        }

        /// An unsatisfiable instance backjumps, so the `pop` hook is reached —
        /// and the emitted DRAT proof is **byte-identical** to the one the
        /// shipping `NullTheory` path produces. That is the strong form of "the
        /// hooks do not perturb the search": not merely the same verdict, the
        /// same derivation.
        #[test]
        fn an_unsatisfiable_search_pops_and_emits_the_same_proof_as_the_null_path() {
            let counts = Rc::new(RefCell::new(HookCounts::default()));
            let f = pigeonhole(5);
            let ProofSolveOutcome::Unsat(expected) = solve_with_drat_proof(&f) else {
                panic!("pigeonhole(5) is unsat");
            };
            let (outcome, steps) = solve_with(&f, CountingTheory(Rc::clone(&counts)));
            assert_eq!(outcome, StreamingProofOutcome::Unsat);
            assert_eq!(
                steps, expected,
                "a hooked search must derive the identical DRAT proof"
            );
            let counts = counts.borrow();
            assert!(counts.pops > 0, "pop hook never reached: {counts:?}");
            assert!(counts.asserts > 0, "assert hook never reached: {counts:?}");
        }

        /// A theory that refuses at `final_check` and then cannot explain the
        /// handle it issued must stop the search with the **undecided**
        /// outcome — never `sat`, and never `unsat` either. This is the guard
        /// that a `final_check` answer is read rather than discarded, and that
        /// an unresolvable explanation is not silently treated as an empty
        /// core (which would be a wrong `unsat`).
        struct RefusingFinalCheck;
        impl NativeTheory for RefusingFinalCheck {
            fn assert(&mut self, _var: usize, _value: bool) -> Result<(), Vec<CnfLit>> {
                Ok(())
            }
            fn push(&mut self) {}
            fn pop(&mut self) {}
            fn propagate_into(&mut self, _queue: &mut PropagationQueue) {}
            fn final_check(&mut self) -> FinalCheckOutcome {
                FinalCheckOutcome::Conflict(TheoryExplanation::Lazy(ExplanationId(7)))
            }
        }

        #[test]
        fn a_final_check_conflict_it_cannot_explain_never_becomes_a_verdict() {
            let f = formula(4, &[&[1, 2], &[-1, 3], &[-2, -3], &[3, 4]]);
            let (outcome, steps) = solve_with(&f, RefusingFinalCheck);
            assert_eq!(
                outcome,
                StreamingProofOutcome::Interrupted,
                "an unexplainable theory conflict is undecided, never sat or unsat"
            );
            assert!(
                steps.is_empty(),
                "no theory lemma may enter the DRAT stream: {steps:?}"
            );
        }

        /// A theory that conflicts on the first assertion with an **empty**
        /// core must stop the search undecided, and must not have emitted an
        /// empty clause. `¬⊤` names nothing to learn from, so acting on it
        /// would be a wrong `unsat` on the theory's say-so with no clause in
        /// the artifact behind it (see `Cdcl::stage_theory_conflict`).
        struct ConflictingAssert;
        impl NativeTheory for ConflictingAssert {
            fn assert(&mut self, _var: usize, _value: bool) -> Result<(), Vec<CnfLit>> {
                Err(Vec::new())
            }
            fn push(&mut self) {}
            fn pop(&mut self) {}
            fn propagate_into(&mut self, _queue: &mut PropagationQueue) {}
        }

        #[test]
        fn an_empty_assert_conflict_core_never_becomes_unsat() {
            let f = pigeonhole(4);
            let (outcome, steps) = solve_with(&f, ConflictingAssert);
            assert_eq!(
                outcome,
                StreamingProofOutcome::Interrupted,
                "an empty conflict core is undecided, never a refutation"
            );
            assert!(
                steps.is_empty(),
                "a declined theory conflict must not emit the empty clause: {steps:?}"
            );
        }

        /// A theory that propagates a literal the Boolean side has already
        /// **falsified** is a theory conflict wearing a propagation's clothes,
        /// and it must be acted on: ignoring a sound theory propagation would
        /// be merely incomplete, but ignoring a theory *conflict* would be
        /// unsound, and both travel this code path.
        ///
        /// The reason clause it hands back, `[~x1]`, is already the conflict
        /// clause -- every literal in it is false, `~x1` included -- which is
        /// the whole reason the module carries explanations in clause form.
        struct FalsifyingTheory;
        impl NativeTheory for FalsifyingTheory {
            fn assert(&mut self, _var: usize, _value: bool) -> Result<(), Vec<CnfLit>> {
                Ok(())
            }
            fn push(&mut self) {}
            fn pop(&mut self) {}
            fn propagate_into(&mut self, queue: &mut PropagationQueue) {
                // Var 0 is fixed TRUE at level zero by the unit clause, so
                // propagating its negation is always a conflict.
                let not_x1 = crate::CnfLit::positive(crate::CnfVar::new(0).unwrap()).negated();
                queue.push_eager(not_x1, vec![not_x1]);
            }
        }

        /// The same theory with the explanation withheld: the conflict is
        /// recognised, cannot be substantiated, and is **declined** rather than
        /// guessed.
        struct UnexplainedFalsifyingTheory;
        impl NativeTheory for UnexplainedFalsifyingTheory {
            fn assert(&mut self, _var: usize, _value: bool) -> Result<(), Vec<CnfLit>> {
                Ok(())
            }
            fn push(&mut self) {}
            fn pop(&mut self) {}
            fn propagate_into(&mut self, queue: &mut PropagationQueue) {
                queue.push_lazy(
                    crate::CnfLit::positive(crate::CnfVar::new(0).unwrap()).negated(),
                    ExplanationId(1),
                );
            }
        }

        #[test]
        fn a_theory_propagation_onto_a_falsified_literal_refutes_modulo_its_lemma() {
            // (1) & (1 | 2): var 0 is true at level zero and the formula is
            // satisfiable, so only the theory can close it.
            let f = formula(2, &[&[1], &[1, 2]]);
            assert!(
                matches!(solve_with_drat_proof(&f), ProofSolveOutcome::Sat(_)),
                "fixture must be Boolean-satisfiable, or the test proves nothing"
            );
            let (outcome, steps, lemmas) = solve_with_lemmas(&f, FalsifyingTheory);
            assert_eq!(outcome, SearchOutcome::Unsat);
            assert_eq!(lemmas.len(), 1, "one enumerated lemma: {lemmas:?}");
            let extended = extended_formula(&f, &lemmas);
            assert_eq!(
                crate::check_drat(&extended, &steps),
                Ok(true),
                "the stream refutes cnf ++ lemmas"
            );
            assert_ne!(
                crate::check_drat(&f, &steps),
                Ok(true),
                "and must NOT refute the bare CNF"
            );
        }

        #[test]
        fn an_unexplained_falsifying_propagation_is_declined_not_guessed() {
            let f = formula(2, &[&[1], &[1, 2]]);
            let (outcome, steps) = solve_with(&f, UnexplainedFalsifyingTheory);
            assert_eq!(
                outcome,
                StreamingProofOutcome::Interrupted,
                "a conflict the theory cannot explain is undecided"
            );
            assert!(steps.is_empty(), "no proof step may be emitted: {steps:?}");
        }

        /// A theory that registers one atom mid-search and then constrains it.
        ///
        /// It polls `take_new_atoms` exactly once with a nonzero count -- a
        /// theory that answered `1` forever would grow the variable table
        /// without bound, which is what `THEORY_STEP_BUDGET` exists to stop and
        /// is not what a real theory does.
        struct AtomRegisteringTheory {
            registered: bool,
            /// The new variable's index, learned from the first `assert` that
            /// mentions it (the driver appends it after every existing var).
            values: Vec<Option<bool>>,
            trail: Vec<usize>,
            marks: Vec<usize>,
        }

        impl AtomRegisteringTheory {
            fn new(vars: usize) -> Self {
                Self {
                    registered: false,
                    values: vec![None; vars + 1],
                    trail: Vec::new(),
                    marks: Vec::new(),
                }
            }
        }

        impl NativeTheory for AtomRegisteringTheory {
            fn assert(&mut self, var: usize, value: bool) -> Result<(), Vec<CnfLit>> {
                self.values[var] = Some(value);
                self.trail.push(var);
                Ok(())
            }
            fn push(&mut self) {
                self.marks.push(self.trail.len());
            }
            fn pop(&mut self) {
                let bound = self.marks.pop().unwrap_or(0);
                while self.trail.len() > bound {
                    let var = self.trail.pop().expect("trail above its own mark");
                    self.values[var] = None;
                }
            }
            fn propagate_into(&mut self, _queue: &mut PropagationQueue) {}
            fn take_new_atoms(&mut self) -> usize {
                if self.registered {
                    0
                } else {
                    self.registered = true;
                    1
                }
            }
            fn final_check(&mut self) -> FinalCheckOutcome {
                // The registered atom (the last variable) must be TRUE. The
                // clause `[v]` is false exactly when it is not.
                let new_var = self.values.len() - 1;
                if self.values[new_var] == Some(false) {
                    let v = crate::CnfLit::positive(crate::CnfVar::new(new_var).unwrap());
                    return FinalCheckOutcome::Conflict(TheoryExplanation::Eager(vec![v]));
                }
                FinalCheckOutcome::Sat
            }
        }

        #[test]
        fn an_atom_registered_mid_search_is_decided_and_constrained() {
            // Two Boolean variables; the theory adds a third and requires it.
            let f = formula(2, &[&[1, 2]]);
            let mut theory = AtomRegisteringTheory::new(2);
            let outcome = solve_with_theory_and_drat_proof(
                &f,
                &mut theory,
                None,
                DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            );
            let TheoryProofOutcome::Sat(model) = outcome else {
                panic!("the extended problem is satisfiable; got {outcome:?}");
            };
            assert_eq!(
                model.values().len(),
                3,
                "the registered atom is a real variable and appears in the model"
            );
            assert!(
                model.values()[2],
                "the theory's final check forces the registered atom true"
            );
            assert_eq!(
                theory.values[2],
                Some(true),
                "and the theory was told about it"
            );
        }

        // ------------------------------------------------------------------
        // The `Theory` reason path (S6): a lazily-explained theory implication
        // that conflict analysis walks past.
        // ------------------------------------------------------------------

        /// The handle `LazyImplyingTheory` issues. Deliberately not 0 and not a
        /// clause id, so a `Reason` that lost its tag would resolve to the
        /// wrong thing rather than to nothing.
        const IMPLY_HANDLE: ExplanationId = ExplanationId(7);

        /// A mock theory whose whole content is the implication
        /// `¬x1 → x3` -- a fact the CNF does not contain.
        ///
        /// It hands the clause back **on demand** (`explain`), which is the
        /// point: the driver stores `Reason::theory(7)` and only materialises
        /// `(x3 ∨ x1)` if conflict analysis actually resolves against it.
        struct LazyImplyingTheory {
            /// What the driver has told us, per variable.
            values: Vec<Option<bool>>,
            /// Assertion trail and its per-decision-level marks, so `pop`
            /// unwinds in lockstep with the driver's backjump.
            trail: Vec<usize>,
            marks: Vec<usize>,
            /// How many times `explain` was called -- the lazy channel's meter.
            explains: usize,
        }

        impl LazyImplyingTheory {
            fn new(vars: usize) -> Self {
                Self {
                    values: vec![None; vars],
                    trail: Vec::new(),
                    marks: Vec::new(),
                    explains: 0,
                }
            }

            /// `x1` (variable 0) as a positive literal.
            fn x1() -> CnfLit {
                crate::CnfLit::positive(crate::CnfVar::new(0).unwrap())
            }

            /// `x3` (variable 2) as a positive literal.
            fn x3() -> CnfLit {
                crate::CnfLit::positive(crate::CnfVar::new(2).unwrap())
            }
        }

        impl NativeTheory for LazyImplyingTheory {
            fn assert(&mut self, var: usize, value: bool) -> Result<(), Vec<CnfLit>> {
                self.values[var] = Some(value);
                self.trail.push(var);
                Ok(())
            }
            fn push(&mut self) {
                self.marks.push(self.trail.len());
            }
            fn pop(&mut self) {
                let bound = self.marks.pop().unwrap_or(0);
                while self.trail.len() > bound {
                    let var = self.trail.pop().expect("trail above its own mark");
                    self.values[var] = None;
                }
            }
            fn propagate_into(&mut self, queue: &mut PropagationQueue) {
                // ¬x1 implies x3, and only while x3 is still open.
                if self.values[0] == Some(false) && self.values[2].is_none() {
                    queue.push_lazy(Self::x3(), IMPLY_HANDLE);
                }
            }
            fn explain(
                &mut self,
                handle: ExplanationId,
                _implied: Option<CnfLit>,
            ) -> Option<Vec<CnfLit>> {
                assert_eq!(
                    handle, IMPLY_HANDLE,
                    "driver asked for a handle we never issued"
                );
                self.explains += 1;
                // The clause `(x3 ∨ x1)`: the implied literal plus the negation
                // of the antecedent `¬x1`.
                Some(vec![Self::x3(), Self::x1()])
            }
        }

        /// The fixture: **Boolean-satisfiable**, and unsatisfiable only once the
        /// theory's `¬x1 → x3` is available. So every step the search takes past
        /// the first conflict depends on the theory lemma being installed, and
        /// the emitted stream cannot be a refutation of the CNF alone.
        ///
        /// ```text
        /// c0 ( x1 | x2)   c1 (~x2 | x4)   c2 (~x3 | ~x4 | x5)
        /// c3 (~x1 | x2)   c4 (~x3 | ~x4 | ~x5)   c5 (~x1 | x3)
        /// ```
        ///
        /// Boolean model: x1=F, x2=T, x4=T, x3=F. With `¬x1 → x3` both branches
        /// close: `x1=F` gives x2,x4,x3 and c2/c4 conflict; `x1=T` gives x2,x4
        /// (c3,c1) and x3 (c5), and c2/c4 conflict again.
        fn lazy_theory_fixture() -> crate::CnfFormula {
            formula(
                5,
                &[
                    &[1, 2],
                    &[-2, 4],
                    &[-3, -4, 5],
                    &[-1, 2],
                    &[-3, -4, -5],
                    &[-1, 3],
                ],
            )
        }

        /// Runs the search keeping the solver alive afterwards, so the
        /// ADR-1704 lemma stream can be read off it.
        fn solve_with_lemmas<T: NativeTheory>(
            f: &crate::CnfFormula,
            theory: T,
        ) -> (SearchOutcome, Vec<crate::DratStep>, Vec<Vec<CnfLit>>) {
            let mut sink = VecProofSink::new();
            let mut cdcl = Cdcl::new_with_theory(f, &mut sink, theory);
            let outcome = cdcl
                .run(&[], None, DEFAULT_PROOF_SAT_CONFLICT_LIMIT)
                .expect("VecProofSink never fails");
            let lemmas = cdcl.theory_lemmas.clone();
            drop(cdcl);
            (outcome, sink.into_steps(), lemmas)
        }

        /// `cnf ++ lemmas`, in that order -- ADR-1704 section 1's extended
        /// formula, built here the way a checker would build it.
        fn extended_formula(f: &crate::CnfFormula, lemmas: &[Vec<CnfLit>]) -> crate::CnfFormula {
            let mut extended = crate::CnfFormula::new(f.variable_count());
            for clause in f.clauses() {
                extended
                    .add_clause(crate::CnfClause::new(clause.lits().to_vec()))
                    .expect("the extended formula has the same variable count");
            }
            for lemma in lemmas {
                extended
                    .add_clause(crate::CnfClause::new(lemma.clone()))
                    .expect("a lemma is over the same variables as the CNF");
            }
            extended
        }

        /// The `Theory` reason is resolved through `explain`, the answer lands
        /// in the arena as an **input** clause (never a learned one, so
        /// `reduce_db` can never delete the justification of an assigned
        /// literal), and conflict analysis carries on through it to a verdict.
        #[test]
        fn a_lazy_theory_reason_is_resolved_into_an_input_clause_and_analysis_continues() {
            let f = lazy_theory_fixture();
            // Control: without the theory the fixture is satisfiable, so the
            // unsat below is the theory's doing and not the formula's.
            assert!(
                matches!(solve_with_drat_proof(&f), ProofSolveOutcome::Sat(_)),
                "fixture must be Boolean-satisfiable, or the test proves nothing"
            );

            let (outcome, steps, lemmas) = solve_with_lemmas(&f, LazyImplyingTheory::new(5));
            assert_eq!(
                outcome,
                SearchOutcome::Unsat,
                "conflict analysis must run through the theory reason to a verdict"
            );
            assert_eq!(
                lemmas.len(),
                1,
                "exactly one theory explanation was resolved: {lemmas:?}"
            );
            let lemma = &lemmas[0];
            assert_eq!(
                lemma[0],
                LazyImplyingTheory::x3(),
                "slot 0 of an installed lemma is the literal it justifies"
            );
            let mut sorted = lemma.clone();
            sorted.sort_by_key(|l| (l.var().index(), l.is_negated()));
            assert_eq!(
                sorted,
                vec![LazyImplyingTheory::x1(), LazyImplyingTheory::x3()],
                "the lemma is the clause the theory handed back"
            );
            assert!(
                steps.iter().all(|step| !matches!(
                    step,
                    crate::DratStep::Add(lits) if *lits == *lemma
                )),
                "a lemma is an INPUT clause; emitting it as a derived DRAT step is \
                 exactly the unlabelled learned clause ADR-1704 forbids: {steps:?}"
            );
        }

        /// ADR-1704 section 1: the Boolean stream is a proof of
        /// `cnf ++ lemmas`, **not** of `cnf`. Both directions are asserted, so
        /// this test cannot pass by the checker accepting everything or by it
        /// refusing everything.
        #[test]
        fn the_boolean_stream_checks_over_the_extended_formula_and_not_over_the_cnf() {
            let f = lazy_theory_fixture();
            let (outcome, steps, lemmas) = solve_with_lemmas(&f, LazyImplyingTheory::new(5));
            assert_eq!(outcome, SearchOutcome::Unsat);
            assert_eq!(lemmas.len(), 1);

            let extended = extended_formula(&f, &lemmas);
            assert_eq!(
                crate::check_drat(&extended, &steps),
                Ok(true),
                "the stream must be a checkable refutation of cnf ++ lemmas"
            );
            assert_ne!(
                crate::check_drat(&f, &steps),
                Ok(true),
                "the same stream must NOT check as a refutation of the bare CNF -- \
                 that is the assurance regression ADR-1704 exists to make visible"
            );
        }

        /// ADR-1704 section 1's counting rule: the lemma count is the
        /// **subtraction on the artifact**, `extended.len() - cnf.len()`, not a
        /// number the producer asserts. A producer that appended its lemmas to
        /// the CNF and reported zero would fail here.
        #[test]
        fn the_theory_lemma_count_is_read_off_the_artifact_not_asserted() {
            let f = lazy_theory_fixture();
            let (_, _, lemmas) = solve_with_lemmas(&f, LazyImplyingTheory::new(5));
            let extended = extended_formula(&f, &lemmas);
            assert_eq!(
                extended.clauses().len() - f.clauses().len(),
                lemmas.len(),
                "extended must be cnf followed by lemmas, nothing interleaved"
            );
            assert_eq!(lemmas.len(), 1, "the counted lemma total for this run");
            // And the extension really is a suffix: the CNF prefix is untouched.
            for (before, after) in f.clauses().iter().zip(extended.clauses()) {
                assert_eq!(before.lits(), after.lits());
            }
        }

        /// The lazy channel is lazy: `explain` is called **once**, when
        /// conflict analysis first walks past the implied literal -- not at
        /// propagation time, and not again after the reason has been rewritten
        /// to a clause. Eager materialisation would call it once per
        /// propagation whether or not it was ever needed.
        #[test]
        fn an_explanation_is_resolved_at_most_once_per_assignment() {
            let f = lazy_theory_fixture();
            let mut sink = VecProofSink::new();
            let theory = LazyImplyingTheory::new(5);
            let mut cdcl = Cdcl::new_with_theory(&f, &mut sink, theory);
            let outcome = cdcl
                .run(&[], None, DEFAULT_PROOF_SAT_CONFLICT_LIMIT)
                .expect("VecProofSink never fails");
            assert_eq!(outcome, SearchOutcome::Unsat);
            assert_eq!(
                cdcl.theory.explains, 1,
                "one resolution for one lemma; the handle is not re-resolved"
            );
            assert_eq!(cdcl.theory_lemmas.len(), cdcl.theory.explains);
        }

        // ------------------------------------------------------------------
        // Theory CONFLICTS (S7): from `assert`, and from `final_check`.
        // ------------------------------------------------------------------

        /// A theory that refuses the combination `x1 & x2`, reporting the
        /// conflict clause `(~x1 | ~x2)` the moment its second assertion
        /// arrives.
        struct MutexTheory;
        impl NativeTheory for MutexTheory {
            fn assert(&mut self, var: usize, value: bool) -> Result<(), Vec<CnfLit>> {
                let _ = (var, value);
                let x1 = crate::CnfLit::positive(crate::CnfVar::new(0).unwrap());
                let x2 = crate::CnfLit::positive(crate::CnfVar::new(1).unwrap());
                if var == 1 && value {
                    return Err(vec![x1.negated(), x2.negated()]);
                }
                Ok(())
            }
            fn push(&mut self) {}
            fn pop(&mut self) {}
            fn propagate_into(&mut self, _queue: &mut PropagationQueue) {}
        }

        /// An `assert` conflict closes the search, and the artifact says what
        /// it assumed. The CNF asserts both atoms, so it is propositionally
        /// satisfiable and the refutation is entirely the theory's.
        #[test]
        fn an_assert_conflict_refutes_modulo_its_enumerated_lemma() {
            let f = formula(2, &[&[1], &[2]]);
            assert!(
                matches!(solve_with_drat_proof(&f), ProofSolveOutcome::Sat(_)),
                "fixture must be Boolean-satisfiable, or the test proves nothing"
            );
            let (outcome, steps, lemmas) = solve_with_lemmas(&f, MutexTheory);
            assert_eq!(outcome, SearchOutcome::Unsat);
            assert_eq!(lemmas.len(), 1, "one enumerated lemma: {lemmas:?}");
            let mut sorted = lemmas[0].clone();
            sorted.sort_by_key(|l| (l.var().index(), l.is_negated()));
            assert_eq!(
                sorted,
                vec![
                    crate::CnfLit::positive(crate::CnfVar::new(0).unwrap()).negated(),
                    crate::CnfLit::positive(crate::CnfVar::new(1).unwrap()).negated(),
                ],
                "the lemma is the clause the theory handed back"
            );
            let extended = extended_formula(&f, &lemmas);
            assert_eq!(crate::check_drat(&extended, &steps), Ok(true));
            assert_ne!(
                crate::check_drat(&f, &steps),
                Ok(true),
                "the same stream must NOT refute the bare CNF"
            );
        }

        /// A theory that rejects **every** total assignment, handing back the
        /// negation of the assignment it was shown. Refuting a satisfiable CNF
        /// this way forces the driver to enumerate, learn and backjump through
        /// the `final_check` conflict path rather than through `assert`.
        struct EnumeratingRefuter {
            values: Vec<Option<bool>>,
            trail: Vec<usize>,
            marks: Vec<usize>,
            final_checks: usize,
        }

        impl EnumeratingRefuter {
            fn new(vars: usize) -> Self {
                Self {
                    values: vec![None; vars],
                    trail: Vec::new(),
                    marks: Vec::new(),
                    final_checks: 0,
                }
            }
        }

        impl NativeTheory for EnumeratingRefuter {
            fn assert(&mut self, var: usize, value: bool) -> Result<(), Vec<CnfLit>> {
                self.values[var] = Some(value);
                self.trail.push(var);
                Ok(())
            }
            fn push(&mut self) {
                self.marks.push(self.trail.len());
            }
            fn pop(&mut self) {
                let bound = self.marks.pop().unwrap_or(0);
                while self.trail.len() > bound {
                    let var = self.trail.pop().expect("trail above its own mark");
                    self.values[var] = None;
                }
            }
            fn propagate_into(&mut self, _queue: &mut PropagationQueue) {}
            fn final_check(&mut self) -> FinalCheckOutcome {
                self.final_checks += 1;
                let mut clause = Vec::new();
                for (var, value) in self.values.iter().enumerate() {
                    let Some(value) = *value else { continue };
                    let positive = crate::CnfLit::positive(crate::CnfVar::new(var).unwrap());
                    // The literal that is FALSE under this assignment.
                    clause.push(if value { positive.negated() } else { positive });
                }
                FinalCheckOutcome::Conflict(TheoryExplanation::Eager(clause))
            }
        }

        /// The `final_check` conflict path: a satisfiable CNF is refuted by a
        /// theory that rejects every model, and the resulting stream checks
        /// over `cnf ++ lemmas` and only over it.
        #[test]
        fn final_check_conflicts_refute_modulo_their_enumerated_lemmas() {
            let f = formula(3, &[&[1, 2], &[-1, 3]]);
            assert!(
                matches!(solve_with_drat_proof(&f), ProofSolveOutcome::Sat(_)),
                "fixture must be Boolean-satisfiable, or the test proves nothing"
            );
            let (outcome, steps, lemmas) = solve_with_lemmas(&f, EnumeratingRefuter::new(3));
            assert_eq!(
                outcome,
                SearchOutcome::Unsat,
                "a theory that rejects every model refutes the query"
            );
            assert!(
                !lemmas.is_empty(),
                "every final-check conflict is an enumerated lemma"
            );
            let extended = extended_formula(&f, &lemmas);
            assert_eq!(
                crate::check_drat(&extended, &steps),
                Ok(true),
                "the stream refutes cnf ++ lemmas"
            );
            assert_ne!(
                crate::check_drat(&f, &steps),
                Ok(true),
                "and must NOT refute the bare CNF"
            );
        }

        /// A theory whose only content is `x1 -> x2`, offered **lazily** at
        /// level zero.
        struct LevelZeroImplier {
            x1: bool,
        }

        const LEVEL_ZERO_HANDLE: ExplanationId = ExplanationId(11);

        impl NativeTheory for LevelZeroImplier {
            fn assert(&mut self, var: usize, value: bool) -> Result<(), Vec<CnfLit>> {
                if var == 0 {
                    self.x1 = value;
                }
                Ok(())
            }
            fn push(&mut self) {}
            fn pop(&mut self) {}
            fn propagate_into(&mut self, queue: &mut PropagationQueue) {
                if self.x1 {
                    queue.push_lazy(
                        crate::CnfLit::positive(crate::CnfVar::new(1).unwrap()),
                        LEVEL_ZERO_HANDLE,
                    );
                }
            }
            fn explain(
                &mut self,
                handle: ExplanationId,
                _implied: Option<CnfLit>,
            ) -> Option<Vec<CnfLit>> {
                assert_eq!(handle, LEVEL_ZERO_HANDLE);
                // The clause `(x2 | ~x1)`.
                Some(vec![
                    crate::CnfLit::positive(crate::CnfVar::new(1).unwrap()),
                    crate::CnfLit::positive(crate::CnfVar::new(0).unwrap()).negated(),
                ])
            }
        }

        /// The level-zero refutation path resolves the lazy theory reasons it
        /// leaned on before emitting the empty clause.
        ///
        /// This is the one shape where conflict analysis never runs -- a
        /// conflict at decision level zero is a refutation outright -- so the
        /// theory implication that produced it is justified by a handle and by
        /// nothing else. `check_drat` replays unit propagation over
        /// `cnf ++ lemmas` and cannot see a handle, so without
        /// `materialize_trail_theory_reasons` the emitted empty clause is not
        /// RUP and the artifact is rejected by its own checker.
        #[test]
        fn a_level_zero_refutation_materialises_the_lazy_reasons_it_leaned_on() {
            // (x1) & (~x2 | x3) & (~x2 | ~x3): satisfiable with x2 false, and
            // closed only once the theory supplies `x1 -> x2`.
            let f = formula(3, &[&[1], &[-2, 3], &[-2, -3]]);
            assert!(
                matches!(solve_with_drat_proof(&f), ProofSolveOutcome::Sat(_)),
                "fixture must be Boolean-satisfiable, or the test proves nothing"
            );
            let (outcome, steps, lemmas) = solve_with_lemmas(&f, LevelZeroImplier { x1: false });
            assert_eq!(outcome, SearchOutcome::Unsat);
            assert_eq!(
                lemmas.len(),
                1,
                "the lazy reason the refutation leaned on is materialised: {lemmas:?}"
            );
            let extended = extended_formula(&f, &lemmas);
            assert_eq!(
                crate::check_drat(&extended, &steps),
                Ok(true),
                "the empty clause must be RUP over cnf ++ lemmas"
            );
            assert_ne!(
                crate::check_drat(&f, &steps),
                Ok(true),
                "and must not be RUP over the bare CNF"
            );
        }

        /// ADR-1704 prohibition 1, enforced where it CAN be: every clause that
        /// entered the database from the theory is enumerated in the lemma
        /// stream.
        ///
        /// The count is read off the **arena** — input clauses (`learned[cid]
        /// == false`) beyond the ones the formula supplied — and not off the
        /// list, so a future lemma installer that forgot to record itself would
        /// fail here rather than quietly shrink the artifact's assumption
        /// count. That is the half of failure mode 4 no propositional checker
        /// can see: a clause carries no provenance once it is in a CNF.
        #[test]
        fn every_theory_origin_clause_is_enumerated() {
            let f = formula(3, &[&[1, 2], &[-1, 3]]);
            let mut sink = VecProofSink::new();
            let mut cdcl = Cdcl::new_with_theory(&f, &mut sink, EnumeratingRefuter::new(3));
            let outcome = cdcl
                .run(&[], None, DEFAULT_PROOF_SAT_CONFLICT_LIMIT)
                .expect("VecProofSink never fails");
            assert_eq!(outcome, SearchOutcome::Unsat);
            let input_clauses_in_arena = cdcl.learned.iter().filter(|l| !**l).count();
            assert_eq!(
                input_clauses_in_arena - f.clauses().len(),
                cdcl.theory_lemmas.len(),
                "every non-learned clause past the formula's own is an enumerated lemma"
            );
            assert!(
                !cdcl.theory_lemmas.is_empty(),
                "the fixture must actually install lemmas, or this measures nothing"
            );
        }

        /// The same run through the public entry point: the artifact is
        /// assembled, its lemma count is the subtraction, and `check()` grades
        /// it `CheckedModuloLemmas` -- never `Verified`.
        #[test]
        fn the_public_entry_point_reports_a_refutation_modulo_counted_lemmas() {
            let f = formula(3, &[&[1, 2], &[-1, 3]]);
            let mut theory = EnumeratingRefuter::new(3);
            let outcome = solve_with_theory_and_drat_proof(
                &f,
                &mut theory,
                None,
                DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            );
            let TheoryProofOutcome::Unsat(artifact) = outcome else {
                panic!("the theory refutes every model; got {outcome:?}");
            };
            let count = artifact.theory_lemma_count();
            assert!(count > 0, "a CDCL(T) refutation assumed something");
            assert_eq!(
                count,
                artifact.lemmas().len(),
                "the count is |extended| - |cnf|, and it agrees with the list"
            );
            assert_eq!(
                artifact.check(),
                crate::TheoryRefutationCheck::CheckedModuloLemmas { lemmas: count },
                "an undischarged lemma is never graded `Verified`"
            );
            assert!(
                theory.final_checks > 0,
                "the theory really was consulted at total assignments"
            );
        }

        /// The control: the identical entry point over a propositionally
        /// unsatisfiable formula, with a theory that never says anything,
        /// produces a **lemma-free** artifact that grades `Verified`. Without
        /// it, `CheckedModuloLemmas` above could be what this route always
        /// returns.
        #[test]
        fn a_theory_that_contributes_nothing_yields_a_verified_lemma_free_artifact() {
            let f = pigeonhole(4);
            let counts = Rc::new(RefCell::new(HookCounts::default()));
            let mut theory = CountingTheory(Rc::clone(&counts));
            let outcome = solve_with_theory_and_drat_proof(
                &f,
                &mut theory,
                None,
                DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            );
            let TheoryProofOutcome::Unsat(artifact) = outcome else {
                panic!("pigeonhole(4) is unsat; got {outcome:?}");
            };
            assert_eq!(artifact.theory_lemma_count(), 0);
            assert_eq!(artifact.check(), crate::TheoryRefutationCheck::Verified);
            assert!(
                counts.borrow().asserts > 0,
                "the theory was attached and driven: {:?}",
                counts.borrow()
            );
        }
    }
}

/// The driver-side instrument, ported from `CdclT` before the engines move
/// (plan slice S7b step 1).
///
/// A swap of one CDCL(T) engine for another is only measurable if the same
/// counters report from both sides, so these tests are about the *instrument*,
/// not about the search: every counter has to be able to move, an unmeasured
/// run has to be distinguishable from a measured zero, and switching the
/// instrument on must not change what the search decides.
#[cfg(test)]
mod layer_stats_tests {
    use super::theory::{FinalCheckOutcome, NativeTheory, PropagationQueue};
    use super::{
        DEFAULT_PROOF_SAT_CONFLICT_LIMIT, LAYER_STATS_MIRROR_INTERVAL, NativeLayerStats,
        NativeLayerStatsMirror, NullTheory, TheoryExplanation, TheoryProofOutcome,
        TheorySolveOptions, TheorySolveOutcome, solve_with_theory_and_drat_proof,
        solve_with_theory_and_drat_proof_impl, solve_with_theory_and_drat_proof_mirrored,
        solve_with_theory_and_drat_proof_traced,
    };
    use crate::{CnfClause, CnfFormula, CnfLit, CnfVar};
    use std::sync::Arc;
    use std::time::Duration;

    fn lit(value: i64) -> CnfLit {
        let var = CnfVar::new(usize::try_from(value.unsigned_abs() - 1).unwrap()).unwrap();
        let positive = CnfLit::positive(var);
        if value < 0 {
            positive.negated()
        } else {
            positive
        }
    }

    fn formula(variable_count: usize, clauses: &[&[i64]]) -> CnfFormula {
        let mut f = CnfFormula::new(variable_count);
        for clause in clauses {
            f.add_clause(CnfClause::new(clause.iter().copied().map(lit).collect()))
                .unwrap();
        }
        f
    }

    /// A theory that rejects **every** total assignment, handing back the
    /// negation of the assignment it was shown, and additionally propagates
    /// `x1 -> x2` so the theory-propagation counter has something to count.
    ///
    /// Refuting a Boolean-satisfiable CNF this way drives every counted path:
    /// decisions, `final_check` calls, theory conflicts, theory propagations,
    /// 1-UIP analyses and learned literals.
    struct Refuter {
        values: Vec<Option<bool>>,
        trail: Vec<usize>,
        marks: Vec<usize>,
    }

    impl Refuter {
        fn new(vars: usize) -> Self {
            Self {
                values: vec![None; vars],
                trail: Vec::new(),
                marks: Vec::new(),
            }
        }
    }

    impl NativeTheory for Refuter {
        fn assert(&mut self, var: usize, value: bool) -> Result<(), Vec<CnfLit>> {
            self.values[var] = Some(value);
            self.trail.push(var);
            Ok(())
        }

        fn push(&mut self) {
            self.marks.push(self.trail.len());
        }

        fn pop(&mut self) {
            let mark = self.marks.pop().unwrap_or(0);
            while self.trail.len() > mark {
                let var = self.trail.pop().expect("trail above mark");
                self.values[var] = None;
            }
        }

        fn propagate_into(&mut self, queue: &mut PropagationQueue) {
            // `x1 = true` implies `x2 = true`, justified by the clause
            // `(x2 | ~x1)` — the implied literal first, every antecedent
            // negated, which is this module's clause convention.
            if self.values[0] == Some(true) && self.values[1].is_none() {
                queue.push_eager(lit(2), vec![lit(2), lit(-1)]);
            }
        }

        fn final_check(&mut self) -> FinalCheckOutcome {
            // The negation of the assignment shown: a legal theory lemma for a
            // theory whose truth is "no total assignment is consistent".
            let clause = self
                .values
                .iter()
                .enumerate()
                .filter_map(|(var, value)| {
                    value.map(|v| {
                        let positive = CnfLit::positive(CnfVar::new(var).unwrap());
                        if v { positive.negated() } else { positive }
                    })
                })
                .collect::<Vec<_>>();
            FinalCheckOutcome::Conflict(TheoryExplanation::Eager(clause))
        }
    }

    /// The fixture, chosen so the CNF alone is satisfiable: whatever refutes it
    /// is the theory, and every theory-side counter has a reason to move.
    fn fixture() -> CnfFormula {
        formula(4, &[&[1, 2], &[-1, 3], &[2, 3, 4], &[-3, -4, 1]])
    }

    fn traced() -> (TheoryProofOutcome, NativeLayerStats) {
        let mut theory = Refuter::new(4);
        solve_with_theory_and_drat_proof_traced(
            &fixture(),
            &mut theory,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
        )
    }

    /// The fixture is Boolean-satisfiable, so the refutation below is the
    /// theory's and the theory-side counters cannot be nonzero for an
    /// uninteresting reason.
    #[test]
    fn the_fixture_cnf_alone_is_satisfiable() {
        assert!(
            matches!(
                super::solve_with_drat_proof(&fixture()),
                super::ProofSolveOutcome::Sat(_)
            ),
            "if the CNF alone were unsat, no theory counter would have to move"
        );
    }

    /// Every driver-side counter this instrument carries moves on a search that
    /// exercises its stage. A counter that could never move is an instrument
    /// that cannot report a regression in the stage it names.
    #[test]
    fn every_driver_side_counter_moves_on_a_theory_search() {
        let (outcome, stats) = traced();
        assert!(
            matches!(outcome, TheoryProofOutcome::Unsat(_)),
            "the theory refutes every total assignment: {outcome:?}"
        );
        assert!(stats.decisions > 0, "decisions: {stats:?}");
        assert!(stats.final_checks > 0, "final_checks: {stats:?}");
        assert!(stats.theory_conflicts > 0, "theory_conflicts: {stats:?}");
        assert!(
            stats.theory_propagations > 0,
            "theory_propagations: {stats:?}"
        );
        assert!(stats.learned_clauses > 0, "learned_clauses: {stats:?}");
        assert!(stats.learned_literals > 0, "learned_literals: {stats:?}");
        assert!(
            stats.learned_literals_before_minimization >= stats.learned_literals,
            "minimization never adds literals: {stats:?}"
        );
        assert!(
            stats.total() > Duration::ZERO,
            "some stage took measurable time: {stats:?}"
        );
        assert!(
            stats.theory_assert > Duration::ZERO,
            "the assert stage was timed: {stats:?}"
        );
        assert!(
            stats.theory_final_check > Duration::ZERO,
            "the final-check stage was timed: {stats:?}"
        );
        assert!(
            stats.conflict_analysis > Duration::ZERO,
            "the analysis stage was timed: {stats:?}"
        );
        assert!(
            stats.boolean_propagate > Duration::ZERO,
            "the Boolean propagation stage was timed: {stats:?}"
        );
        assert!(
            stats.theory_push_pop > Duration::ZERO,
            "the push/pop stage was timed: {stats:?}"
        );
    }

    /// An **unmeasured** run reports all zeros, so a caller can never mistake
    /// "collection was off" for "the stage cost nothing". The untraced entry
    /// point is the one every shipping route uses; if it accumulated counters
    /// silently, the zero-vs-absent distinction would be gone and so would the
    /// claim that a default run reads no clock.
    #[test]
    fn an_untraced_solve_reports_the_all_zero_snapshot() {
        // The traced arm proves these same counters are nonzero on this exact
        // fixture, so the control below is live and not vacuous.
        let (_, traced_stats) = traced();
        assert!(traced_stats.decisions > 0, "{traced_stats:?}");
        let mut untraced_theory = Refuter::new(4);
        let (outcome, untraced_stats) = solve_with_theory_and_drat_proof_impl(
            &fixture(),
            &mut untraced_theory,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            super::TheorySolveOptions::default(),
            None,
        );
        assert!(
            matches!(outcome, super::TheorySolveOutcome::Unsat(Some(_))),
            "{outcome:?}"
        );
        assert_eq!(
            untraced_stats,
            NativeLayerStats::default(),
            "an unmeasured run must be all-zero, not a partial measurement"
        );
    }

    /// The instrument does not change what the search decides. Same fixture,
    /// same theory, tracing on and off: the same verdict, the same lemma count
    /// and the same Boolean stream. Timing hooks are output-only by
    /// construction; this is that property checked rather than argued.
    #[test]
    fn tracing_changes_neither_the_verdict_nor_the_boolean_stream() {
        let (traced_outcome, _) = traced();
        let mut theory = Refuter::new(4);
        let untraced_outcome = solve_with_theory_and_drat_proof(
            &fixture(),
            &mut theory,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
        );
        let (TheoryProofOutcome::Unsat(a), TheoryProofOutcome::Unsat(b)) =
            (&traced_outcome, &untraced_outcome)
        else {
            panic!("both arms must refute: {traced_outcome:?} / {untraced_outcome:?}");
        };
        assert_eq!(a.theory_lemma_count(), b.theory_lemma_count());
        assert_eq!(a.boolean_stream(), b.boolean_stream());
    }

    /// `restarts` is derived from `restart_count`, not counted at the restart
    /// site. It must read zero on a search that never restarted, or the
    /// "completed restarts" name is off by one. Paired with the nonzero
    /// assertions above, so an always-zero derivation cannot pass as a
    /// measurement.
    #[test]
    fn restarts_reads_zero_on_a_search_that_never_restarted() {
        let (_, stats) = traced();
        assert_eq!(
            stats.restarts, 0,
            "this fixture decides in far fewer conflicts than the first restart interval"
        );
    }

    /// `NullTheory` is what every shipping entry point uses. Tracing it must
    /// leave every *theory* counter at zero while the Boolean ones still move —
    /// the instrument's own statement that the theory half vanishes at
    /// monomorphization.
    #[test]
    fn a_null_theory_search_moves_only_the_boolean_counters() {
        let mut theory = NullTheory;
        let (outcome, stats) = solve_with_theory_and_drat_proof_traced(
            &formula(2, &[&[1, 2], &[-1, 2], &[1, -2], &[-1, -2]]),
            &mut theory,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
        );
        assert!(
            matches!(outcome, TheoryProofOutcome::Unsat(_)),
            "{outcome:?}"
        );
        assert_eq!(stats.theory_conflicts, 0);
        assert_eq!(stats.theory_propagations, 0);
        assert_eq!(stats.final_checks, 0, "HAS_THEORY is false: no check runs");
        assert_eq!(stats.theory_assert, Duration::ZERO);
        assert_eq!(stats.theory_final_check, Duration::ZERO);
        assert_eq!(stats.theory_push_pop, Duration::ZERO);
        assert!(stats.decisions > 0, "the Boolean side still decides");
        assert!(stats.learned_clauses > 0, "and still learns: {stats:?}");
    }

    /// A fixture whose search takes far more than `LAYER_STATS_MIRROR_INTERVAL`
    /// theory iterations, so a mirror has to have been written to *during* the
    /// search rather than at the end of one.
    ///
    /// Seven independent `(a | b)` clauses over fourteen variables: the CNF has
    /// `3^7 = 2187` models and [`Refuter`] refutes each in turn, so the search
    /// loop runs thousands of iterations no matter how the heuristics order
    /// them. Deterministic — no wall clock anywhere in the test.
    fn long_running_fixture() -> CnfFormula {
        formula(
            14,
            &[
                &[1, 2],
                &[3, 4],
                &[5, 6],
                &[7, 8],
                &[9, 10],
                &[11, 12],
                &[13, 14],
            ],
        )
    }

    fn traced_options() -> TheorySolveOptions {
        TheorySolveOptions {
            collect_layer_stats: true,
            // The artifact is irrelevant here and holding thousands of learned
            // clauses is the expensive part of this fixture.
            record_proof: false,
            ..TheorySolveOptions::default()
        }
    }

    /// The property the mirror exists for: counters are readable from a slot
    /// the search wrote to *while it was running*, not only from the value it
    /// returns.
    ///
    /// A caller that never gets the return value — an external watchdog that
    /// gives up on the worker thread — has nothing else. This test stands in
    /// for that caller without racing a clock: it reads the mirror after the
    /// search returns, but a sample can only be there because a flush happened
    /// mid-search, which is exactly what the `flushes` count and the
    /// strictly-smaller-than-final counters below pin.
    #[test]
    fn a_running_search_mirrors_partial_counters_before_it_returns() {
        let mirror = Arc::new(NativeLayerStatsMirror::new());
        let mut theory = Refuter::new(14);
        let (outcome, complete) = solve_with_theory_and_drat_proof_mirrored(
            &long_running_fixture(),
            &mut theory,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            traced_options(),
            Some(Arc::clone(&mirror)),
        );
        assert!(
            matches!(outcome, TheorySolveOutcome::Unsat(_)),
            "{outcome:?}"
        );
        let (partial, flushes) = mirror
            .sample()
            .expect("a search this long must have flushed the mirror at least once");
        assert!(flushes > 0, "a sample exists, so a flush produced it");
        assert!(
            partial.decisions > 0,
            "a mirrored sample must carry real counters, not an empty struct: {partial:?}"
        );
        // The mirrored reading is a MID-search state, so every monotone counter
        // it carries is at most the completed one. Equality would mean the only
        // flush was effectively the final state, which this fixture is sized to
        // rule out.
        assert!(
            partial.decisions < complete.decisions,
            "mirrored {partial:?} is a partial state of completed {complete:?}"
        );
        assert!(partial.final_checks < complete.final_checks, "{partial:?}");
    }

    /// The mirror is silent when collection is off, so a mirrored sample is
    /// never a run of measured zeros — the same "an unmeasured run is not a
    /// measured zero" rule the rest of this module enforces on the return
    /// value.
    #[test]
    fn a_mirror_without_collection_is_never_written() {
        let mirror = Arc::new(NativeLayerStatsMirror::new());
        let mut theory = Refuter::new(14);
        let _ = solve_with_theory_and_drat_proof_mirrored(
            &long_running_fixture(),
            &mut theory,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            TheorySolveOptions {
                collect_layer_stats: false,
                record_proof: false,
                ..TheorySolveOptions::default()
            },
            Some(Arc::clone(&mirror)),
        );
        assert!(
            mirror.sample().is_none(),
            "collection was off: nothing was measured, so nothing may be reported"
        );
    }

    /// Passing no mirror leaves the verdict and the completed counters exactly
    /// where they were — the mirror is an output-only side channel.
    #[test]
    fn mirroring_changes_neither_the_verdict_nor_the_completed_counters() {
        let mut with_theory = Refuter::new(14);
        let (with_outcome, with_stats) = solve_with_theory_and_drat_proof_mirrored(
            &long_running_fixture(),
            &mut with_theory,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            traced_options(),
            Some(Arc::new(NativeLayerStatsMirror::new())),
        );
        let mut without_theory = Refuter::new(14);
        let (without_outcome, without_stats) = solve_with_theory_and_drat_proof_mirrored(
            &long_running_fixture(),
            &mut without_theory,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
            traced_options(),
            None,
        );
        assert_eq!(
            core::mem::discriminant(&with_outcome),
            core::mem::discriminant(&without_outcome)
        );
        assert_eq!(with_stats.decisions, without_stats.decisions);
        assert_eq!(with_stats.final_checks, without_stats.final_checks);
        assert_eq!(with_stats.learned_clauses, without_stats.learned_clauses);
    }

    /// The cadence constant is what bounds how stale a sample can be, so it is
    /// pinned rather than left to drift: a sample is at most this many theory
    /// iterations behind the search.
    #[test]
    fn the_mirror_cadence_is_the_deadline_check_cadence() {
        assert_eq!(LAYER_STATS_MIRROR_INTERVAL, super::DEADLINE_CHECK_INTERVAL);
    }
}

/// What the driver asks a lazy handle FOR (plan slice S7b).
///
/// A handle can stand for two different things and the difference is invisible
/// to a theory that materialises its own clauses — which is every fixture in
/// this file, and why nothing here could fail on it before. It is entirely
/// visible to an adapter over a channel that carries *asserted* literals
/// (`axeyum_solver::euf_egraph::TheorySolver`), where a conflict core becomes a
/// clause by negating every literal and a propagation reason becomes one by
/// negating every antecedent and then adding the implied literal back.
///
/// Ask for a conflict core where a reason was meant and that literal is
/// dropped. The resulting clause is **stronger than the theory entails** —
/// `~antecedents` instead of `~antecedents \/ implied` — and it is installed as
/// an ADR-1704 *input* clause of the extended formula, so refuting that formula
/// would be a wrong `unsat`. Found by the S7b engine differential
/// (`axeyum_solver::native_cdclt`), which disagreed on 39 of 8,000 runs.
#[cfg(test)]
mod explain_contract_tests {
    use super::theory::{
        ExplanationId, FinalCheckOutcome, NativeTheory, PropagationQueue, TheoryExplanation,
    };
    use super::{DEFAULT_PROOF_SAT_CONFLICT_LIMIT, solve_with_theory_and_drat_proof};
    use crate::{CnfClause, CnfFormula, CnfLit, CnfVar};
    use std::cell::RefCell;
    use std::rc::Rc;

    fn lit(value: i64) -> CnfLit {
        let var = CnfVar::new(usize::try_from(value.unsigned_abs() - 1).unwrap()).unwrap();
        let positive = CnfLit::positive(var);
        if value < 0 {
            positive.negated()
        } else {
            positive
        }
    }

    fn formula(variable_count: usize, clauses: &[&[i64]]) -> CnfFormula {
        let mut f = CnfFormula::new(variable_count);
        for clause in clauses {
            f.add_clause(CnfClause::new(clause.iter().copied().map(lit).collect()))
                .unwrap();
        }
        f
    }

    /// A theory that lazily propagates `x2` once `x1` is asserted true, with
    /// `x1` as its only antecedent, and records what the driver asked each
    /// handle for.
    struct RecordingLazyImplier {
        asked: Rc<RefCell<Vec<Option<CnfLit>>>>,
        x1_true: bool,
    }

    impl NativeTheory for RecordingLazyImplier {
        fn assert(&mut self, var: usize, value: bool) -> Result<(), Vec<CnfLit>> {
            if var == 0 {
                self.x1_true = value;
            }
            Ok(())
        }

        fn push(&mut self) {}

        fn pop(&mut self) {}

        fn propagate_into(&mut self, queue: &mut PropagationQueue) {
            if self.x1_true {
                queue.push_lazy(lit(2), ExplanationId(7));
            }
        }

        fn final_check(&mut self) -> FinalCheckOutcome {
            FinalCheckOutcome::Sat
        }

        fn explain(
            &mut self,
            handle: ExplanationId,
            implied: Option<CnfLit>,
        ) -> Option<Vec<CnfLit>> {
            assert_eq!(handle, ExplanationId(7));
            self.asked.borrow_mut().push(implied);
            // The reason CLAUSE for `x1 -> x2`, which contains the implied
            // literal. An asserted-literal channel would have returned `[x1]`
            // and relied on `implied` to rebuild this.
            Some(vec![lit(2), lit(-1)])
        }
    }

    /// The propagate-onto-an-already-false-literal path asks for the literal's
    /// **reason**, so it must name that literal. Before this was threaded the
    /// call passed `None`, i.e. "give me a conflict core", and an adapter
    /// obeying that would have installed a clause the theory does not entail.
    #[test]
    fn a_propagation_onto_a_false_literal_asks_for_the_reason_not_a_core() {
        // `(x1)` and `(~x2)` are both level-zero units, so by the time the
        // theory round runs, `x2` is already FALSE and the theory's propagation
        // of `x2` lands on it. That is the path under test.
        let f = formula(2, &[&[1], &[-2]]);
        let asked = Rc::new(RefCell::new(Vec::new()));
        let mut theory = RecordingLazyImplier {
            asked: Rc::clone(&asked),
            x1_true: false,
        };
        let _ = solve_with_theory_and_drat_proof(
            &f,
            &mut theory,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
        );
        let asked = asked.borrow();
        assert!(
            !asked.is_empty(),
            "the fixture must reach the propagate-onto-false path at all"
        );
        assert!(
            asked.iter().all(|implied| *implied == Some(lit(2))),
            "every ask on this path names the implied literal, got {asked:?}"
        );
    }

    /// The companion case: a handle standing for a `final_check` **conflict
    /// core** is asked for with `None`. Without this the test above would pass
    /// for a driver that named a literal everywhere, which would break the
    /// other direction of the translation just as badly.
    #[test]
    fn a_final_check_conflict_handle_is_asked_for_as_a_core() {
        struct LazyRefuter {
            asked: Rc<RefCell<Vec<Option<CnfLit>>>>,
        }
        impl NativeTheory for LazyRefuter {
            fn assert(&mut self, _var: usize, _value: bool) -> Result<(), Vec<CnfLit>> {
                Ok(())
            }
            fn push(&mut self) {}
            fn pop(&mut self) {}
            fn propagate_into(&mut self, _queue: &mut PropagationQueue) {}
            fn final_check(&mut self) -> FinalCheckOutcome {
                FinalCheckOutcome::Conflict(TheoryExplanation::Lazy(ExplanationId(3)))
            }
            fn explain(
                &mut self,
                handle: ExplanationId,
                implied: Option<CnfLit>,
            ) -> Option<Vec<CnfLit>> {
                assert_eq!(handle, ExplanationId(3));
                self.asked.borrow_mut().push(implied);
                // `~x1 \/ ~x2`: every literal false under the total assignment
                // the fixture's two units force.
                Some(vec![lit(-1), lit(-2)])
            }
        }
        let f = formula(2, &[&[1], &[2]]);
        let asked = Rc::new(RefCell::new(Vec::new()));
        let mut theory = LazyRefuter {
            asked: Rc::clone(&asked),
        };
        let _ = solve_with_theory_and_drat_proof(
            &f,
            &mut theory,
            None,
            DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
        );
        let asked = asked.borrow();
        assert!(!asked.is_empty(), "the fixture must reach `final_check`");
        assert!(
            asked.iter().all(Option::is_none),
            "a conflict core names no implied literal, got {asked:?}"
        );
    }
}
