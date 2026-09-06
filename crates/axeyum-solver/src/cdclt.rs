//! Generic online CDCL(T) driver (Track 1, P1.5 slice a).
//!
//! A CDCL search over the Boolean skeleton of a quantifier-free query where a
//! [`TheorySolver`] runs **online**: each trail assignment of a theory atom is
//! notified to the theory as it happens ([`TheorySolver::assert`]), theory
//! propagations are enqueued as implied literals carrying their theory-explained
//! reasons ([`TheorySolver::propagate`]), theory conflicts become learned clauses
//! via the explained core, and the theory is pushed/popped in lockstep with the
//! search's decision levels ([`TheorySolver::push`]/[`TheorySolver::pop`]).
//!
//! [`CdclT`] is parameterised over any `T: TheorySolver`. The same driver now serves
//! EUF, strings, pure LIA/LRA, and the live EUF+LIA/EUF+LRA combined theories; the
//! adapters retain responsibility for model construction and original-assertion replay.
//!
//! Final-check refinements may reserve Boolean variables before search or append
//! dormant theory variables after search has started. Initial theory atoms occupy
//! the first SAT-variable slots, but appended atoms can follow Tseitin auxiliaries;
//! an explicit bidirectional map keeps SAT variables and theory atom indices aligned.
//! [`CdclT::add_permanent_clause`] activates the variables named by a valid
//! refinement clause, preserves the current learned-clause database, phase state,
//! and variable activities, and lets the next [`CdclT::solve`] call resume from the
//! retained search state. A caller may also activate appended atoms directly when
//! their semantics are enforced by the theory itself, as with EUF congruence.
//!
//! ## Conflict learning — 1-UIP over the mixed implication graph
//! Both Boolean input clauses and theory clauses (a theory conflict `¬⋀core` or a
//! theory propagation `¬reason ∨ lit`, both entailed by the theory alone) live in
//! one clause database and one implication graph. Conflict analysis is standard
//! **1-UIP** resolution against that mixed graph ([`CdclT::analyze_conflict`]) with
//! non-chronological backjumping. This is the full first cut, not the
//! restart-on-theory-conflict fallback: the theory reason clauses are small (an
//! e-graph `explain` core), so 1-UIP over them stays cheap and yields short
//! asserting clauses — the same scheme the already-validated embedded EUF loop uses.
//!
//! ## Soundness posture
//! - `Unsat` is returned only when 1-UIP derives the empty asserting clause at
//!   decision level 0 — a resolution refutation over input clauses and
//!   theory-entailed clauses. The theory clauses come from the *same* EUF
//!   explanation machinery ([`axeyum_egraph::EGraph::explain`], independently
//!   re-checked by [`axeyum_egraph::check_congruence`] on the offline route) that
//!   the landed `check_qf_uf` path already relies on; this slice adds **no new**
//!   unsat trust surface. Tests gate every online `Unsat` against the offline route.
//! - `Sat` is *not* trusted from the driver: the caller assembles a model from the
//!   theory and **replays** it against the original assertions, downgrading to
//!   `Unknown` on any non-replay.
//! - Learned-clause reduction is satisfiability-preserving: only redundant 1-UIP
//!   resolvents are tombstoned. Original clauses, low-LBD glue clauses, and every
//!   clause currently serving as a trail reason are retained. Dynamically inserted
//!   permanent clauses are theory-valid constraints and are retained with the input
//!   clauses; dormant variables cannot affect search until a valid refinement
//!   activates them. Appending a mapped theory variable does not renumber any
//!   existing SAT variable, clause, trail entry, or learned reason.
//! - Deterministic: conflict-side VSIDS selects the highest-activity unassigned
//!   variable with lowest-index ties, phase saving reuses its last polarity, Luby
//!   restarts are a pure function of conflict count, and LBD reduction uses a total
//!   value/recency/slot order over stable clause slots. Every search data structure
//!   is a `Vec`; there is no hash-iteration order or clock-derived choice. The only
//!   clock read is the deadline check.
//! - Deadline: `deadline` is checked at the head of the search loop and of the
//!   propagation fixpoint, so the search degrades to `Unknown` under a deterministic
//!   resource bound (the deadline-hole class is designed out).
//! - Step budget (defense in depth): the main [`CdclT::solve`] loop also counts its
//!   iterations against a [`CdclT::step_budget`] and degrades to [`Outcome::Unknown`]
//!   on exhaustion. The driver is provably terminating for a well-behaved theory —
//!   the trigger-literal invariant (every theory conflict carries a current-level
//!   literal) makes every conflict force a strict backjump, so learning cannot
//!   repeat a trail state — but the theories driven here are **incomplete and
//!   non-monotone** (`StringTheory` re-runs its refuter per assert and may report a
//!   conflict at assert *k* it missed at *k-1*). The step budget is the belt to the
//!   deadline's braces: when no deadline is configured (e.g. `wasm32`, or a
//!   `SolverConfig` with no timeout) it still guarantees the loop cannot spin
//!   forever on a pathological theory. Exhaustion is *sound* — `Unknown` is always a
//!   permitted verdict — never a wrong sat/unsat.

use std::cell::Cell;
use std::collections::VecDeque;
use std::time::{Duration, Instant};

use crate::euf_egraph::{
    ExplanationId, FinalCheckOutcome, PropagationQueue, TheoryExplanation, TheoryLit, TheorySolver,
};
use crate::layers::TheoryLayerStats;

thread_local! {
    /// Whether the *next* [`CdclT::new`] should collect [`TheoryLayerStats`]
    /// timing. Scoped this way (rather than threaded through the ~10
    /// `CdclT::new` call sites across the arithmetic/EUF/string/combined
    /// theory adapters) for the same reason `nra_real_root::ISOLATE_DEADLINE`
    /// is thread-local: one opt-in knob at the top of a solve, read at the
    /// handful of internal construction points, instead of a parameter
    /// threaded through every adapter. See [`TheoryLayerStatsGuard`].
    static COLLECT_LAYER_STATS: Cell<bool> = const { Cell::new(false) };
    /// The [`TheoryLayerStats`] collected by the most recently completed
    /// [`CdclT::solve`] call while collection was enabled. `None` until
    /// collection has been enabled and a search has completed.
    static LAST_THEORY_LAYER_STATS: Cell<Option<TheoryLayerStats>> = const { Cell::new(None) };
}

/// Enables [`TheoryLayerStats`] collection for every `CdclT` search
/// constructed for the lifetime of the returned guard, restoring the previous
/// setting on drop (so nested/recursive solves compose correctly). Off by
/// default: constructing no guard means no extra clock read beyond the
/// existing deadline check.
///
/// ```ignore
/// let _guard = TheoryLayerStatsGuard::enable();
/// let _ = axeyum_solver::solve_smtlib(text, &config);
/// let stats = last_theory_layer_stats(); // Some(..) if a CDCL(T) route ran
/// ```
pub struct TheoryLayerStatsGuard(bool);

impl TheoryLayerStatsGuard {
    /// Enables collection for the lifetime of the returned guard.
    #[must_use]
    pub fn enable() -> Self {
        TheoryLayerStatsGuard(COLLECT_LAYER_STATS.with(|c| c.replace(true)))
    }
}

impl Drop for TheoryLayerStatsGuard {
    fn drop(&mut self) {
        COLLECT_LAYER_STATS.with(|c| c.set(self.0));
    }
}

/// The [`TheoryLayerStats`] collected by the most recently completed
/// [`CdclT::solve`] call on this thread while a [`TheoryLayerStatsGuard`] was
/// active. `None` if collection was never enabled, or no CDCL(T) search has
/// completed yet on this thread.
#[must_use]
pub fn last_theory_layer_stats() -> Option<TheoryLayerStats> {
    LAST_THEORY_LAYER_STATS.with(Cell::get)
}

/// A CNF literal in the online skeleton: a variable index and its polarity.
/// Initial theory atoms occupy the first slots, while dynamically added theory
/// variables may follow ordinary Tseitin auxiliaries; [`CdclT`] keeps the explicit
/// atom/variable mapping.
///
/// Declared `pub` (rather than `pub(crate)`) only so [`crate::bench_internals`]
/// can re-export it for `benches/cdclt_propagate.rs`; the containing `cdclt`
/// module stays crate-private and the re-export path is gated behind the
/// `bench-internals` feature, so this is not reachable from an ordinary
/// dependent of the crate. Do not use this type outside the driver or a bench.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Lit {
    /// The variable index.
    pub var: usize,
    /// `true` for the positive literal, `false` for its negation.
    pub positive: bool,
}

impl Lit {
    /// The literal over the same variable with flipped polarity.
    fn negate(self) -> Self {
        Self {
            var: self.var,
            positive: !self.positive,
        }
    }
}

/// The result of a CDCL(T) search.
///
/// `pub` for the same bench-only reason as [`Lit`]: reachable outside the
/// crate only through [`crate::bench_internals`], gated by the
/// `bench-internals` feature.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// The skeleton is UNSAT under the theory (a resolution refutation reached the
    /// empty clause at level 0).
    Unsat,
    /// A Boolean- and theory-consistent total assignment was reached; the theory is
    /// left in that satisfying state for the caller to build a model from.
    Sat,
    /// The deadline elapsed before the search closed (a deterministic give-up).
    Unknown,
}

/// How a variable came to be assigned, so backtracking can undo theory state in
/// lockstep with decisions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Cause {
    /// A branching decision; its level owns a matching theory `push`.
    Decision,
    /// Forced by unit propagation, a theory propagation, or a learned unit.
    Implied,
}

/// A conflict surfaced by propagation: the falsified clause to analyse, tagged with
/// whether it is a theory clause (entailed by the theory alone) so the theory-lemma
/// provenance can be tracked through 1-UIP resolution.
struct Conflict {
    clause: Vec<Lit>,
    is_theory: bool,
}

/// The watch-list index of a literal: `2 * var + (0 for positive, 1 for
/// negative)`. Ported verbatim from [`axeyum_cnf`]'s proof-producing core
/// (`proof_sat.rs`'s `lit_code`) so the later engine unification (ADR-1701
/// slice 4 / plan slice S7) is a deletion rather than a reconciliation of two
/// watch schemes.
#[inline]
fn lit_code(lit: Lit) -> usize {
    2 * lit.var + usize::from(!lit.positive)
}

/// One entry in a literal's watch list (the `MiniSat`/`BatSat` blocking-literal
/// scheme, ported verbatim from `proof_sat.rs`). `clause` is the watched
/// clause's id; `blocker` is a *cached* literal of that clause OTHER than the
/// watched one. In [`CdclT::unit_propagate`], if `blocker` is already true under
/// the current assignment the clause is satisfied and is skipped *without
/// dereferencing the clause arena* — the cache hit that makes BCP fast. The
/// blocker is purely a performance hint: it never changes which propagations or
/// conflicts are derived.
#[derive(Clone, Copy)]
struct Watch {
    clause: usize,
    blocker: Lit,
}

/// Per-clause index into the packed literal arena ([`CdclT::arena`]). Mirrors
/// `proof_sat.rs`'s `ClauseHeader` (in turn `BatSat`'s
/// `ClauseAllocator`/`ClauseHeader`): all clause literals live contiguously in
/// one cache-local arena, and each clause is described by its `(offset, len)`
/// here rather than by a separately heap-allocated `Vec`. The two watched
/// literals are kept in arena slots `offset+0` and `offset+1` (the slot-0/1
/// convention), which is what makes [`CdclT::rebuild_watches`] a faithful
/// re-derivation of the current watch state rather than a reset of it.
///
/// Clause ids never move: `headers` only grows (learned and permanent clauses
/// are appended) and deletion is by tombstone, so an id recorded in a watch or
/// in [`CdclT::reason_clause`] stays valid for the whole search.
#[derive(Clone, Copy)]
struct ClauseHeader {
    offset: usize,
    len: usize,
}

/// Defense-in-depth ceiling on [`CdclT::solve`] main-loop iterations when no
/// deadline is configured. The driver is terminating for a well-behaved theory;
/// this bound only bites on a pathological non-monotone theory that would
/// otherwise spin. It is deliberately large — orders of magnitude beyond what any
/// skeleton this driver receives today needs — so a legitimate search is never
/// capped, yet a true livelock still ends (in bounded, if large, time) as a sound
/// `Unknown`. Callers with a real problem should also set `config.timeout`, which
/// is the primary bound.
const DEFAULT_STEP_BUDGET: usize = 16_000_000;

/// VSIDS activity decay. Growing the bump increment by `1 / VSIDS_DECAY`
/// makes recent conflicts weigh more without scanning every activity.
const VSIDS_DECAY: f64 = 0.95;
/// Common rescale factor used before activity values approach floating-point
/// overflow. Multiplying every value preserves the decision order.
const VSIDS_RESCALE: f64 = 1e-100;
/// Activity ceiling that triggers a common rescale.
const VSIDS_RESCALE_LIMIT: f64 = 1e100;

/// Conflict interval unit multiplied by the current Luby value. The production
/// schedule matches the arithmetic-local and proof-producing CDCL engines.
const LUBY_UNIT: usize = 100;

/// Live learned clauses tolerated before the first database reduction.
const REDUCE_FIRST: usize = 2_000;
/// Additive growth of the live learned-clause budget after each reduction.
const REDUCE_INCREMENT: usize = 300;
/// Clauses at or below this literal-block distance are permanent glue clauses.
const GLUE_LBD: usize = 2;

/// Trail literals [`CdclT::unit_propagate`] processes between two deadline
/// reads. Small enough that the deadline-blind window stays negligible next to
/// a seconds-scale budget, large enough that the clock is not read once per
/// propagated literal.
const DEADLINE_CHECK_LITERALS: usize = 256;

/// The 1-indexed Luby sequence `1,1,2,1,1,2,4,...` in reluctant-doubling form.
fn luby(mut index: u64) -> u64 {
    let mut exponent = 1_u64;
    loop {
        let power = 1_u64 << exponent;
        if index == power - 1 {
            return 1_u64 << (exponent - 1);
        }
        let half = 1_u64 << (exponent - 1);
        if half <= index && index < power - 1 {
            index = index - half + 1;
            exponent = 1;
        } else {
            exponent += 1;
        }
    }
}

/// The outcome of one conflict-learning step.
enum Learn {
    /// The asserting clause was learned and the UIP enqueued; keep searching.
    Continue,
    /// The conflict was implied at level 0: UNSAT.
    Unsat,
    /// A theory failed to resolve a deferred explanation handle it emitted
    /// (ADR-1701). The search abandons with [`Outcome::Unknown`] — sound, never
    /// a verdict.
    Abort,
}

/// What [`CdclT::run_final_check`] decided at a total Boolean assignment
/// (ADR-1701).
enum FinalCheck {
    /// The theory accepted the assignment: the search is `Sat`.
    Sat,
    /// The theory's conflict was implied at level 0: the search is `Unsat`.
    Unsat,
    /// The theory could not complete the check, or could not explain its own
    /// conflict: the search degrades to `Unknown`.
    Unknown,
    /// The conflict was learned and the search backjumped: keep searching.
    Continue,
}

/// A generic online CDCL(T) search over a CNF skeleton, driving any
/// [`TheorySolver`] online with 1-UIP theory-conflict learning, theory propagation,
/// non-chronological backjumping, and deadline-bounded termination.
///
/// `pub` for the same bench-only reason as [`Lit`]: reachable outside the
/// crate only through [`crate::bench_internals`], gated by the
/// `bench-internals` feature. Fields stay `pub(crate)`/private; a bench
/// drives this only through [`CdclT::new`] and [`CdclT::solve`].
pub struct CdclT {
    var_count: usize,
    /// Per SAT variable, the aligned theory atom when this variable is mirrored
    /// into the theory. Dynamic theory variables may follow Tseitin auxiliaries.
    theory_atom_for_var: Vec<Option<usize>>,
    /// Per theory atom, its SAT variable. This maps theory explanations and
    /// propagations back into the mixed Boolean implication graph.
    theory_var_for_atom: Vec<usize>,
    /// Variables currently owned by the search. Reserved theory atoms may remain
    /// inactive until a final-check lemma names them.
    active: Vec<bool>,
    /// Flat, cache-local arena of every clause's literals (input clauses first,
    /// permanent and learned clauses appended). Clause `cid` occupies the
    /// contiguous slice `arena[h.offset .. h.offset + h.len]` for its
    /// [`ClauseHeader`] `h`. The arena only grows, so an already-registered
    /// clause's slice never relocates. Slots `offset+0` and `offset+1` hold the
    /// clause's two currently watched literals.
    arena: Vec<Lit>,
    /// Per-clause `(offset, len)` headers into [`Self::arena`], indexed by
    /// clause id. `headers.len()` is the clause count.
    headers: Vec<ClauseHeader>,
    /// Per-literal watch lists, indexed by [`lit_code`]; `2 * var_count` long.
    /// Each entry carries a blocking literal (see [`Watch`]).
    watches: Vec<Vec<Watch>>,
    /// Index into [`Self::trail`] of the next assignment whose watch list has
    /// not been scanned yet. Clamped on backjump so an unpropagated literal is
    /// never skipped.
    qhead: usize,
    /// Clauses registered after construction (or shorter than two literals) that
    /// still need one assignment-aware evaluation before the watch machinery can
    /// carry them. Drained at the head of [`Self::unit_propagate`]; see
    /// [`Self::add_permanent_clause`].
    pending_clauses: VecDeque<usize>,
    /// Current value per variable (`None` if unassigned).
    value: Vec<Option<bool>>,
    /// Trail of `(var, value, cause)` in assignment order.
    trail: Vec<(usize, bool, Cause)>,
    /// Per variable: the decision level it was assigned at (valid while assigned).
    level: Vec<usize>,
    /// Per variable: a **materialised** reason clause that forced it. `None` for
    /// a decision, and also `None` for a Boolean implication, whose reason is the
    /// clause-database entry recorded in [`Self::reason_clause`] — that clause is
    /// read straight out of [`Self::arena`] by [`Self::reason_for`] instead of
    /// being cloned at every implication. Only theory-derived reasons (which have
    /// no clause-database entry) are stored here.
    reason: Vec<Option<Vec<Lit>>>,
    /// Per variable: whether its reason clause is a theory clause. A 1-UIP clause
    /// resolved only through theory clauses is itself a theory lemma.
    reason_theory: Vec<bool>,
    /// Stored clause currently serving as each assigned variable's reason, when
    /// that reason came from the clause database. It is both the reason itself
    /// (materialised on demand by [`Self::reason_for`]) and the lock that
    /// protects a learned clause from reduction.
    reason_clause: Vec<Option<usize>>,
    /// Current decision level.
    decision_level: usize,
    /// When set, the search returns [`Outcome::Unknown`] once the deadline passes.
    deadline: Option<Instant>,
    /// Defense-in-depth ceiling on main-loop iterations (see
    /// [`DEFAULT_STEP_BUDGET`]); the search degrades to [`Outcome::Unknown`] when
    /// [`Self::steps`] reaches it.
    step_budget: usize,
    /// Main-loop iterations taken so far (telemetry + the step-budget counter).
    steps: usize,
    /// Set once the step budget was exhausted, so a caller/test can distinguish a
    /// budget-driven `Unknown` from a deadline- or fixpoint-driven one.
    step_budget_hit: bool,
    /// Number of literals assigned by theory propagation. Internal telemetry for
    /// routing/tests; decisions and Boolean unit propagation are not counted.
    theory_propagations: usize,
    /// VSIDS activity per variable. Conflict analysis bumps each variable when it
    /// first enters the conflict side; decisions choose the maximum activity with
    /// deterministic lowest-index ties.
    activity: Vec<f64>,
    /// Current VSIDS bump increment. It grows once per conflict so old activity
    /// decays relative to newly implicated variables.
    var_inc: f64,
    /// Last assigned polarity per variable. Initialized to the previous
    /// true-first behavior and retained across backtracking.
    saved_phase: Vec<bool>,
    /// Conflicts analyzed since the last restart.
    conflicts_since_restart: usize,
    /// 1-indexed position in the Luby schedule. The completed restart count is
    /// `restart_index - 1`.
    restart_index: u64,
    /// Test-only restart-unit override used to force or disable restarts on small
    /// deterministic fixtures.
    #[cfg(test)]
    restart_unit_override: Option<usize>,
    /// Number of original clauses. Slots at or beyond this index are learned and
    /// deletion-eligible subject to glue/lock protection.
    num_original: usize,
    /// Literal-block distance aligned with `clauses` (`0` for originals).
    lbd: Vec<usize>,
    /// Monotone recency stamp aligned with `clauses` (`0.0` for originals).
    clause_activity: Vec<f64>,
    /// Tombstone flag aligned with `clauses`; deleted slots are never reused.
    deleted: Vec<bool>,
    /// Next monotone learned-clause recency stamp.
    clause_increment: f64,
    /// Number of live learned clauses.
    learned_live: usize,
    /// Completed learned-clause database reductions.
    reductions: usize,
    /// Test-only first-reduction budget override.
    #[cfg(test)]
    reduce_first_override: Option<usize>,
    /// Whether this search collects [`TheoryLayerStats`] timing (read once at
    /// construction from [`COLLECT_LAYER_STATS`]). When `false`, every
    /// `time_*`/stage-timing field below stays at its initial `Duration::ZERO`
    /// — no extra `Instant::now()` call is made.
    collect_layer_stats: bool,
    /// Time inside Boolean unit propagation passes (`Self::unit_propagate`).
    time_boolean_propagate: Duration,
    /// Time inside `TheorySolver::assert` calls.
    time_theory_assert: Duration,
    /// Time inside `TheorySolver::propagate` calls.
    time_theory_propagate: Duration,
    /// Time inside `TheorySolver::push`/`pop` calls.
    time_theory_push_pop: Duration,
    /// Time inside 1-UIP conflict analysis (`Self::analyze_conflict`).
    time_conflict_analysis: Duration,
    /// Time inside `TheorySolver::final_check` calls (ADR-1701).
    time_theory_final_check: Duration,
    /// Time inside `TheorySolver::explain` calls resolving deferred explanation
    /// handles (ADR-1701).
    time_theory_explain: Duration,
    /// Conflicts whose falsified clause traces to a theory inconsistency
    /// (`Conflict::is_theory`), as opposed to a purely Boolean conflict.
    /// Counted unconditionally (a plain increment, not a clock read).
    theory_conflicts: usize,
    /// Search decisions taken (`Self::pick_unassigned` choices). Counted
    /// unconditionally.
    decisions: usize,
    /// Completed [`TheorySolver::final_check`] calls (ADR-1701). Counted
    /// unconditionally; stays `0` for every theory keeping the trait default,
    /// because the driver still calls it — the *default body* is what does
    /// nothing. (It is counted so a diagnosis can tell "never reached a total
    /// assignment" from "reached one and the theory accepted it".)
    final_checks: usize,
    /// Per variable, the **deferred** explanation handle behind its theory
    /// propagation, when the theory chose not to materialise the reason
    /// (ADR-1701). `reason[var]` is `None` exactly while this is `Some`;
    /// `Self::reason_for` resolves it on first use and moves it into `reason`.
    /// Cleared in lockstep with `reason` on backjump, so a handle never outlives
    /// the theory state that justifies it.
    deferred_reason: Vec<Option<ExplanationId>>,
    /// The driver-owned propagation queue (ADR-1701), reused across every
    /// propagation fixpoint iteration so a theory that overrides
    /// `propagate_into` allocates nothing per call.
    prop_queue: PropagationQueue,
    /// Set when a theory could not resolve a handle it emitted. The search then
    /// returns [`Outcome::Unknown`] — sound, never a verdict — rather than
    /// treating a missing explanation as an empty clause.
    explanation_unresolved: bool,
}

impl CdclT {
    /// Builds a search over `clauses` on `var_count` variables. The first
    /// `theory_atom_count` variables are theory atoms aligned by index with the
    /// [`TheorySolver`]; later dynamic theory variables use an explicit mapping.
    /// `deadline`, when set, bounds the search.
    ///
    /// `pub` bench-only (see the type doc); reachable outside the crate only
    /// via [`crate::bench_internals`].
    ///
    /// # Panics
    ///
    /// Panics if `theory_atom_count > var_count` (a caller bug: there cannot be
    /// more theory atoms than variables).
    pub fn new(
        var_count: usize,
        theory_atom_count: usize,
        clauses: Vec<Vec<Lit>>,
        deadline: Option<Instant>,
    ) -> Self {
        assert!(theory_atom_count <= var_count);
        let num_original = clauses.len();
        let mut theory_atom_for_var = vec![None; var_count];
        for (atom, slot) in theory_atom_for_var
            .iter_mut()
            .take(theory_atom_count)
            .enumerate()
        {
            *slot = Some(atom);
        }
        // Pack every clause's literals contiguously into one arena, recording a
        // `(offset, len)` header per clause. This mirrors the prior
        // `Vec<Vec<Lit>>` content exactly (same clauses, same order, same
        // intra-clause literal order); only the storage layout differs.
        let mut arena: Vec<Lit> = Vec::with_capacity(clauses.iter().map(Vec::len).sum());
        let mut headers: Vec<ClauseHeader> = Vec::with_capacity(clauses.len());
        for clause in clauses {
            headers.push(ClauseHeader {
                offset: arena.len(),
                len: clause.len(),
            });
            arena.extend(clause);
        }
        // Nothing is assigned at construction, so watching the first two
        // literals is correct without any assignment-aware slot selection --
        // exactly what `proof_sat.rs`'s `Cdcl::new` does. Clauses shorter than
        // two literals carry no watch and are handed to the pending queue, which
        // evaluates them against the assignment at the head of the first
        // propagation.
        let mut watches: Vec<Vec<Watch>> = vec![Vec::new(); 2 * var_count];
        let mut pending_clauses: VecDeque<usize> = VecDeque::new();
        for (cid, header) in headers.iter().enumerate() {
            if header.len < 2 {
                pending_clauses.push_back(cid);
                continue;
            }
            let (l0, l1) = (arena[header.offset], arena[header.offset + 1]);
            watches[lit_code(l0)].push(Watch {
                clause: cid,
                blocker: l1,
            });
            watches[lit_code(l1)].push(Watch {
                clause: cid,
                blocker: l0,
            });
        }
        Self {
            var_count,
            theory_atom_for_var,
            theory_var_for_atom: (0..theory_atom_count).collect(),
            active: vec![true; var_count],
            arena,
            headers,
            watches,
            qhead: 0,
            pending_clauses,
            value: vec![None; var_count],
            trail: Vec::new(),
            level: vec![0; var_count],
            reason: vec![None; var_count],
            reason_theory: vec![false; var_count],
            reason_clause: vec![None; var_count],
            decision_level: 0,
            deadline,
            step_budget: DEFAULT_STEP_BUDGET,
            steps: 0,
            step_budget_hit: false,
            theory_propagations: 0,
            activity: vec![0.0; var_count],
            var_inc: 1.0,
            saved_phase: vec![true; var_count],
            conflicts_since_restart: 0,
            restart_index: 1,
            #[cfg(test)]
            restart_unit_override: None,
            num_original,
            lbd: vec![0; num_original],
            clause_activity: vec![0.0; num_original],
            deleted: vec![false; num_original],
            clause_increment: 1.0,
            learned_live: 0,
            reductions: 0,
            #[cfg(test)]
            reduce_first_override: None,
            collect_layer_stats: COLLECT_LAYER_STATS.with(Cell::get),
            time_boolean_propagate: Duration::ZERO,
            time_theory_assert: Duration::ZERO,
            time_theory_propagate: Duration::ZERO,
            time_theory_push_pop: Duration::ZERO,
            time_conflict_analysis: Duration::ZERO,
            time_theory_final_check: Duration::ZERO,
            time_theory_explain: Duration::ZERO,
            theory_conflicts: 0,
            decisions: 0,
            final_checks: 0,
            deferred_reason: vec![None; var_count],
            prop_queue: PropagationQueue::new(),
            explanation_unresolved: false,
        }
    }

    /// Marks `variables` inactive until [`Self::add_permanent_clause`] activates
    /// them. Clauses supplied to [`Self::new`] must not reference an inactive
    /// variable.
    pub(crate) fn with_inactive_variables(mut self, variables: &[usize]) -> Self {
        for &variable in variables {
            assert!(
                variable < self.var_count,
                "inactive variable is out of range"
            );
            self.active[variable] = false;
        }
        debug_assert!(self.arena.iter().all(|lit| self.active[lit.var]));
        self
    }

    /// Appends one dormant theory variable after every existing SAT variable and
    /// returns `(variable, atom)`. The explicit mapping lets final-check growth
    /// preserve existing Tseitin variable numbers and learned clauses.
    pub(crate) fn add_theory_variable(&mut self) -> (usize, usize) {
        let variable = self.var_count;
        let atom = self.theory_var_for_atom.len();
        self.var_count += 1;
        self.theory_atom_for_var.push(Some(atom));
        self.theory_var_for_atom.push(variable);
        self.active.push(false);
        // Two watch lists per variable (positive and negative literal), keeping
        // `watches` indexable by `lit_code` for every variable that exists.
        self.watches.push(Vec::new());
        self.watches.push(Vec::new());
        self.value.push(None);
        self.level.push(0);
        self.reason.push(None);
        self.reason_theory.push(false);
        self.reason_clause.push(None);
        self.deferred_reason.push(None);
        self.activity.push(0.0);
        self.saved_phase.push(true);
        (variable, atom)
    }

    /// Returns the SAT variable aligned with `atom`, when registered.
    pub(crate) fn theory_variable(&self, atom: usize) -> Option<usize> {
        self.theory_var_for_atom.get(atom).copied()
    }

    /// Activates variables previously reserved or appended dormant.
    pub(crate) fn activate_variables(&mut self, variables: &[usize]) {
        for &variable in variables {
            assert!(
                variable < self.var_count,
                "activated variable is out of range"
            );
            self.active[variable] = true;
        }
    }

    /// Adds a permanent clause and activates every variable it names. This is the
    /// final-check insertion boundary: the current trail and learned database are
    /// retained, and a subsequent [`Self::solve`] resumes from that state.
    ///
    /// Unlike [`Self::new`]'s clauses, this one is registered **under a partial
    /// or total assignment** (the caller has just seen an `Outcome::Sat` it means
    /// to exclude), so its watches cannot simply be the first two literals: they
    /// are chosen assignment-aware by [`Self::attach_clause`], and the clause is
    /// queued for one full evaluation in [`Self::unit_propagate`] so that a
    /// clause which is already unit implies, and one which is already falsified
    /// conflicts, before the watch machinery takes over.
    pub(crate) fn add_permanent_clause(&mut self, clause: Vec<Lit>) {
        let variables = clause.iter().map(|lit| lit.var).collect::<Vec<_>>();
        self.activate_variables(&variables);
        // Consumes `clause` into the arena; the same append `Self::alloc_clause`
        // performs for a borrowed slice.
        let offset = self.arena.len();
        let len = clause.len();
        self.arena.extend(clause);
        let cid = self.headers.len();
        self.headers.push(ClauseHeader { offset, len });
        // LBD zero keeps a post-construction clause out of learned-clause
        // reduction even though it sits beyond `num_original`.
        self.lbd.push(0);
        self.clause_activity.push(0.0);
        self.deleted.push(false);
        self.attach_clause(cid);
        self.pending_clauses.push_back(cid);
    }

    /// The literals of clause `cid`, as a cache-local slice into the arena.
    #[inline]
    fn lits(&self, cid: usize) -> &[Lit] {
        let h = self.headers[cid];
        &self.arena[h.offset..h.offset + h.len]
    }

    /// Appends a clause's literals to the arena and pushes its header, returning
    /// the new clause's stable id. The arena only grows here, so no existing
    /// clause slice moves.
    fn alloc_clause(&mut self, lits: &[Lit]) -> usize {
        let offset = self.arena.len();
        self.arena.extend_from_slice(lits);
        let cid = self.headers.len();
        self.headers.push(ClauseHeader {
            offset,
            len: lits.len(),
        });
        cid
    }

    /// Installs the two watches of clause `cid` **under the current
    /// assignment**, ordering the arena so that slots 0 and 1 hold them.
    ///
    /// The selection rule is the standard one: a literal that is not currently
    /// false is preferred, and among false literals the one assigned at the
    /// highest decision level wins (it is the last to be undone by a backjump).
    /// With that order, if slot 1 is false then every literal outside the two
    /// watches is false as well, so the clause is unit on slot 0 (or falsified
    /// when slot 0 is false too) -- which is exactly what the pending-clause
    /// evaluation in [`Self::unit_propagate`] then acts on. A clause shorter than
    /// two literals carries no watch; the pending queue is what propagates it.
    fn attach_clause(&mut self, cid: usize) {
        let h = self.headers[cid];
        if h.len < 2 {
            return;
        }
        for slot in 0..2 {
            let mut best = slot;
            for k in slot + 1..h.len {
                if self.watch_rank(self.arena[h.offset + k])
                    > self.watch_rank(self.arena[h.offset + best])
                {
                    best = k;
                }
            }
            self.arena.swap(h.offset + slot, h.offset + best);
        }
        let (l0, l1) = (self.arena[h.offset], self.arena[h.offset + 1]);
        self.watches[lit_code(l0)].push(Watch {
            clause: cid,
            blocker: l1,
        });
        self.watches[lit_code(l1)].push(Watch {
            clause: cid,
            blocker: l0,
        });
    }

    /// How good a watch `lit` is under the current assignment: a non-false
    /// literal outranks every false one, and a false literal assigned deeper
    /// outranks a shallower one. Used only by [`Self::attach_clause`].
    fn watch_rank(&self, lit: Lit) -> (bool, usize) {
        match self.lit_sat(lit) {
            Some(false) => (false, self.level[lit.var]),
            _ => (true, 0),
        }
    }

    /// Rebuilds every watch list from scratch over the live (non-tombstoned)
    /// clauses, watching arena slots 0 and 1 of each -- the same clauses the
    /// lists already held, minus the tombstoned ones. This is a faithful
    /// re-derivation rather than a reset because slots 0 and 1 always hold the
    /// clause's *current* watched literals: [`Self::unit_propagate`] swaps a
    /// replacement literal into slot 1 whenever it moves a watch, and
    /// [`Self::attach_clause`] establishes the convention for a clause
    /// registered mid-search. Called after [`Self::reduce_db`] so that no watch
    /// list names a tombstoned clause.
    fn rebuild_watches(&mut self) {
        for list in &mut self.watches {
            list.clear();
        }
        for cid in 0..self.headers.len() {
            if self.deleted[cid] {
                continue;
            }
            let h = self.headers[cid];
            if h.len < 2 {
                continue;
            }
            let (l0, l1) = (self.arena[h.offset], self.arena[h.offset + 1]);
            self.watches[lit_code(l0)].push(Watch {
                clause: cid,
                blocker: l1,
            });
            self.watches[lit_code(l1)].push(Watch {
                clause: cid,
                blocker: l0,
            });
        }
    }

    /// Backtracks every decision while retaining level-zero assignments, input and
    /// permanent clauses, learned clauses, activities, and saved phases. Dynamic
    /// theories may append root-scope terms/atoms after this returns.
    pub(crate) fn backtrack_to_root<T: TheorySolver>(&mut self, theory: &mut T) {
        self.backjump_to(theory, 0);
    }

    /// Current SAT-variable count, including dynamic theory variables.
    pub(crate) fn variable_count(&self) -> usize {
        self.var_count
    }

    /// Current permanent, input, and learned clause-slot count.
    pub(crate) fn clause_count(&self) -> usize {
        self.headers.len()
    }

    /// Overrides the defense-in-depth step budget (see [`DEFAULT_STEP_BUDGET`]).
    /// Used by the non-monotone-theory property tests to detect a livelock with a
    /// tight, deterministic ceiling; production uses the generous default.
    #[cfg(test)]
    pub(crate) fn with_step_budget(mut self, budget: usize) -> Self {
        self.step_budget = budget;
        self
    }

    /// Overrides the Luby schedule unit for a deterministic restart test.
    #[cfg(test)]
    fn with_restart_unit(mut self, unit: usize) -> Self {
        self.restart_unit_override = Some(unit);
        self
    }

    /// Number of completed restarts. Used by tests and by
    /// [`Self::theory_layer_stats`].
    fn restarts(&self) -> u64 {
        self.restart_index - 1
    }

    /// Overrides the first learned-clause reduction budget for a small fixture.
    #[cfg(test)]
    fn with_reduce_first(mut self, first: usize) -> Self {
        self.reduce_first_override = Some(first);
        self
    }

    /// Number of completed learned-clause database reductions.
    #[cfg(test)]
    fn reductions(&self) -> usize {
        self.reductions
    }

    /// Number of tombstoned learned clauses.
    #[cfg(test)]
    fn deleted_learned(&self) -> usize {
        self.deleted[self.num_original..]
            .iter()
            .filter(|&&deleted| deleted)
            .count()
    }

    /// No active variable may name a tombstoned clause as its reason.
    #[cfg(test)]
    fn no_deleted_active_reason(&self) -> bool {
        self.reason_clause
            .iter()
            .enumerate()
            .all(|(var, reason)| match reason {
                Some(clause) => self.value[var].is_none() || !self.deleted[*clause],
                None => true,
            })
    }

    /// Whether the last [`Self::solve`] ended by exhausting the step budget (rather
    /// than the deadline or a real verdict).
    #[cfg(test)]
    pub(crate) fn step_budget_hit(&self) -> bool {
        self.step_budget_hit
    }

    /// Number of literals assigned by theory propagation during the last solve.
    pub(crate) fn theory_propagations(&self) -> usize {
        self.theory_propagations
    }

    /// The current value of `var` (for the caller's model-assembly injection path).
    pub(crate) fn value(&self, var: usize) -> Option<bool> {
        self.value[var]
    }

    /// Whether the deadline (if any) has elapsed.
    fn timed_out(&self) -> bool {
        self.deadline.is_some_and(|d| Instant::now() >= d)
    }

    fn lit_sat(&self, lit: Lit) -> Option<bool> {
        self.value[lit.var].map(|v| v == lit.positive)
    }

    /// The literal currently true for `var` (its trail polarity).
    fn true_literal(&self, var: usize) -> Lit {
        Lit {
            var,
            positive: self.value[var].expect("assigned variable has a value"),
        }
    }

    /// Assigns `var := value` at the current decision level, recording its level and
    /// reason and mirroring a theory atom into the theory. Returns the theory
    /// conflict core if the assertion is inconsistent.
    fn assign<T: TheorySolver>(
        &mut self,
        theory: &mut T,
        var: usize,
        value: bool,
        cause: Cause,
        reason: Option<Vec<Lit>>,
        reason_is_theory: bool,
    ) -> Result<(), Vec<TheoryLit>> {
        self.value[var] = Some(value);
        self.saved_phase[var] = value;
        self.level[var] = self.decision_level;
        self.reason[var] = reason;
        self.reason_theory[var] = reason_is_theory;
        self.reason_clause[var] = None;
        self.trail.push((var, value, cause));
        if let Some(atom) = self.theory_atom_for_var[var] {
            if self.collect_layer_stats {
                let started = Instant::now();
                let outcome = theory.assert(atom, value);
                self.time_theory_assert += started.elapsed();
                outcome?;
            } else {
                theory.assert(atom, value)?;
            }
        }
        Ok(())
    }

    /// Evaluates every clause queued by [`Self::add_permanent_clause`] (and every
    /// input clause shorter than two literals) against the current assignment,
    /// which the watch machinery on its own cannot do: a clause registered
    /// mid-search may already be unit or falsified with no further assignment
    /// coming to trigger its watches, and a clause of fewer than two literals has
    /// no watches at all.
    ///
    /// Returns a falsified clause as a Boolean conflict, exactly as the previous
    /// whole-database rescan did. The queue is drained from the front, so a
    /// conflict leaves the not-yet-examined clauses queued for the next call; a
    /// clause is examined here at most once, and after that its watches carry it.
    fn drain_pending_clauses<T: TheorySolver>(&mut self, theory: &mut T) -> Result<(), Conflict> {
        while let Some(cid) = self.pending_clauses.pop_front() {
            if self.deleted[cid] {
                continue;
            }
            let mut unassigned: Option<Lit> = None;
            let mut satisfied = false;
            let mut count = 0_usize;
            for &lit in self.lits(cid) {
                match self.lit_sat(lit) {
                    Some(true) => {
                        satisfied = true;
                        break;
                    }
                    Some(false) => {}
                    None => {
                        unassigned = Some(lit);
                        count += 1;
                    }
                }
            }
            if satisfied {
                continue;
            }
            if count == 0 {
                return Err(Conflict {
                    clause: self.lits(cid).to_vec(),
                    is_theory: false,
                });
            }
            if count == 1 {
                let lit = unassigned.expect("count == 1 has the unit literal");
                let asserted =
                    self.assign(theory, lit.var, lit.positive, Cause::Implied, None, false);
                // Recorded whether or not the theory accepted the assertion: a
                // rejected assertion still leaves the literal on the trail, and
                // 1-UIP analysis of the resulting theory conflict may have to
                // resolve on it, which needs its reason.
                self.reason_clause[lit.var] = Some(cid);
                if let Err(core) = asserted {
                    return Err(Conflict {
                        clause: self.theory_conflict_clause(&core),
                        is_theory: true,
                    });
                }
            }
        }
        Ok(())
    }

    /// Boolean unit propagation to fixpoint by **two-watched literals with
    /// blocking literals** -- the `MiniSat`/`BatSat` BCP, ported verbatim from
    /// `axeyum-cnf`'s proof-producing core (`proof_sat.rs`'s `propagate`) so that
    /// moving this driver onto that core later is a deletion rather than a
    /// reconciliation of two watch schemes. Returns a falsified conflict clause
    /// on a Boolean conflict, or a learned theory-conflict clause on a forced
    /// theory inconsistency (tagged accordingly).
    ///
    /// Only the newly assigned literals are examined (`qhead .. trail.len()`),
    /// and for each one only the clauses watching its negation, instead of the
    /// whole clause database once per fixpoint pass. The watch list of the
    /// now-false literal is scanned with an in-place `i` (read) / `j` (write)
    /// compaction:
    ///
    /// 1. If a watch's cached `blocker` is already true, the clause is satisfied;
    ///    keep the watch and skip *without touching the clause arena* -- the fast
    ///    path that most watches take.
    /// 2. Otherwise dereference the clause, put the false literal at slot 1, and:
    ///    - if the other watched literal (slot 0) is true, keep the watch
    ///      (refreshing its blocker to that literal) and continue;
    ///    - else look for a non-false replacement literal to watch -- if found,
    ///      move the watch to that literal's list (blocker = the slot-0 literal);
    ///    - else the clause is unit/conflicting: keep the watch (blocker = the
    ///      slot-0 literal). If slot 0 is false it is a conflict; otherwise
    ///      assign slot 0 as a unit implication with this clause as its reason.
    ///
    /// Blocking literals only reduce the *work* of finding propagations and
    /// conflicts; the derived implications and conflicts are identical to the
    /// plain scheme.
    ///
    /// The scanned watch list is moved out of `self` for the duration of the scan
    /// (so the arena, the assignment and the *other* watch lists stay borrowable)
    /// and is put back on **every** exit path, including the theory-conflict one:
    /// a list left behind would silently lose the propagations its clauses owe.
    #[allow(
        clippy::too_many_lines,
        reason = "one BCP loop, kept line-for-line with proof_sat.rs's `propagate` so slice S7 is a deletion"
    )]
    fn unit_propagate<T: TheorySolver>(&mut self, theory: &mut T) -> Result<(), Conflict> {
        self.drain_pending_clauses(theory)?;
        // Deadline check on entry, and then once per `DEADLINE_CHECK_LITERALS`
        // dequeued trail literals: a propagation fixpoint on a very large
        // skeleton is otherwise the search's largest deadline-blind unit.
        // Returning early is sound: the caller's loop re-checks the deadline
        // immediately and degrades to `Unknown`.
        if self.timed_out() {
            return Ok(());
        }
        let mut since_deadline_check = 0_usize;
        while self.qhead < self.trail.len() {
            since_deadline_check += 1;
            if since_deadline_check >= DEADLINE_CHECK_LITERALS {
                since_deadline_check = 0;
                if self.timed_out() {
                    return Ok(());
                }
            }
            let (var, value, _) = self.trail[self.qhead];
            self.qhead += 1;
            let false_lit = Lit {
                var,
                positive: !value,
            };
            let code = lit_code(false_lit);

            let mut watchers = std::mem::take(&mut self.watches[code]);
            let end = watchers.len();
            let mut i = 0_usize;
            let mut j = 0_usize;
            let mut outcome: Result<(), Conflict> = Ok(());
            'clauses: while i < end {
                // (1) Fast path: a true blocker means the clause is satisfied;
                // keep the watch and move on without inspecting the clause.
                let blocker = watchers[i].blocker;
                if self.lit_sat(blocker) == Some(true) {
                    watchers[j] = watchers[i];
                    j += 1;
                    i += 1;
                    continue;
                }

                let cid = watchers[i].clause;
                // Keep the falsified literal at slot 1 (arena slot offset+1).
                let off = self.headers[cid].offset;
                if self.arena[off] == false_lit {
                    self.arena.swap(off, off + 1);
                }
                i += 1;

                // (2) If the other watched literal is true, the clause is
                // satisfied; keep this watch with its blocker refreshed to it.
                let first = self.arena[off];
                if first != blocker && self.lit_sat(first) == Some(true) {
                    watchers[j] = Watch {
                        clause: cid,
                        blocker: first,
                    };
                    j += 1;
                    continue;
                }

                // Look for a non-false literal to watch instead of `false_lit`.
                let len = self.headers[cid].len;
                for k in 2..len {
                    if self.lit_sat(self.arena[off + k]) != Some(false) {
                        self.arena.swap(off + 1, off + k);
                        // Move the watch to the new literal's list; its blocker
                        // is the surviving (slot-0) watched literal. This watch
                        // is dropped from the current list (not copied to `j`).
                        // The replacement is not false and `false_lit` is, so the
                        // destination list is never the one being scanned.
                        let new_code = lit_code(self.arena[off + 1]);
                        self.watches[new_code].push(Watch {
                            clause: cid,
                            blocker: first,
                        });
                        continue 'clauses;
                    }
                }

                // No replacement: the clause is unit or conflicting under the
                // current assignment. Keep this watch (blocker = slot-0 literal).
                watchers[j] = Watch {
                    clause: cid,
                    blocker: first,
                };
                j += 1;
                if self.lit_sat(first) == Some(false) {
                    // Conflict: stop scanning, but preserve the remaining (not
                    // yet visited) watches by copying them down to `j`.
                    outcome = Err(Conflict {
                        clause: self.lits(cid).to_vec(),
                        is_theory: false,
                    });
                    while i < end {
                        watchers[j] = watchers[i];
                        j += 1;
                        i += 1;
                    }
                    break;
                }
                let asserted = self.assign(
                    theory,
                    first.var,
                    first.positive,
                    Cause::Implied,
                    None,
                    false,
                );
                // Recorded whether or not the theory accepted the assertion: a
                // rejected assertion still leaves the literal on the trail, and
                // 1-UIP analysis of the resulting theory conflict may have to
                // resolve on it, which needs its reason.
                self.reason_clause[first.var] = Some(cid);
                if let Err(core) = asserted {
                    // The theory rejected the implication. Same treatment as a
                    // Boolean conflict: keep the unvisited watches.
                    outcome = Err(Conflict {
                        clause: self.theory_conflict_clause(&core),
                        is_theory: true,
                    });
                    while i < end {
                        watchers[j] = watchers[i];
                        j += 1;
                        i += 1;
                    }
                    break;
                }
            }
            watchers.truncate(j);
            self.watches[code] = watchers;
            outcome?;
        }
        Ok(())
    }

    /// Materialises `explanation` into literals, resolving a deferred handle
    /// through [`TheorySolver::explain`] (ADR-1701). `None` means the theory
    /// could not resolve a handle it emitted: a theory bug, recorded so the
    /// search degrades to [`Outcome::Unknown`] instead of learning from a
    /// reason nobody can state.
    fn resolve_explanation<T: TheorySolver>(
        &mut self,
        theory: &mut T,
        explanation: TheoryExplanation,
    ) -> Option<Vec<TheoryLit>> {
        match explanation {
            TheoryExplanation::Eager(lits) => Some(lits),
            TheoryExplanation::Lazy(handle) => {
                let resolved = if self.collect_layer_stats {
                    let started = Instant::now();
                    let resolved = theory.explain(handle);
                    self.time_theory_explain += started.elapsed();
                    resolved
                } else {
                    theory.explain(handle)
                };
                if resolved.is_none() {
                    self.explanation_unresolved = true;
                }
                resolved
            }
        }
    }

    /// The reason clause of an implied literal, resolving a deferred theory
    /// explanation on first use and caching it in `reason` (ADR-1701). `None`
    /// only when a theory failed to resolve its own handle.
    fn reason_for<T: TheorySolver>(&mut self, theory: &mut T, var: usize) -> Option<Vec<Lit>> {
        if let Some(reason) = &self.reason[var] {
            return Some(reason.clone());
        }
        // A Boolean implication's reason is the clause-database entry that forced
        // it. Reading it here -- on the conflict-analysis path, which visits a
        // small fraction of the trail -- replaces the clone that the previous
        // whole-database rescan paid at *every* implication.
        if let Some(cid) = self.reason_clause[var] {
            return Some(self.lits(cid).to_vec());
        }
        let handle = self.deferred_reason[var]?;
        let atom = self.theory_atom_for_var[var]
            .expect("a deferred reason belongs to a theory-mapped variable");
        let value = self.value[var].expect("a deferred reason belongs to an assigned variable");
        let reason_lits = self.resolve_explanation(theory, TheoryExplanation::Lazy(handle))?;
        let clause = self.theory_reason_clause(&reason_lits, TheoryLit { atom, value });
        self.reason[var] = Some(clause.clone());
        self.deferred_reason[var] = None;
        Some(clause)
    }

    /// Registers the theory atoms created since the previous call (ADR-1701):
    /// one appended, activated SAT variable each. A theory keeping the trait
    /// default reports `0`, so this is a single comparison per fixpoint round.
    fn register_new_atoms<T: TheorySolver>(&mut self, theory: &mut T) {
        let fresh = theory.take_new_atoms();
        for _ in 0..fresh {
            let (variable, _atom) = self.add_theory_variable();
            self.active[variable] = true;
        }
    }

    /// Applies sound theory propagations to the trail until fixpoint. Returns the
    /// learned theory-conflict clause on a theory conflict, else `Ok(())`.
    fn theory_propagate<T: TheorySolver>(&mut self, theory: &mut T) -> Result<(), Conflict> {
        loop {
            self.register_new_atoms(theory);
            // Take the driver-owned queue so `self` stays freely borrowable while
            // the batch is applied; it goes back at the end of the iteration with
            // its allocation intact (ADR-1701).
            let mut queue = std::mem::take(&mut self.prop_queue);
            queue.clear();
            if self.collect_layer_stats {
                let started = Instant::now();
                theory.propagate_into(&mut queue);
                self.time_theory_propagate += started.elapsed();
            } else {
                theory.propagate_into(&mut queue);
            }
            let mut progress = false;
            let mut outcome = Ok(());
            for (lit, explanation) in queue.drain() {
                // Intra-batch deadline check (see `unit_propagate`): each
                // applied propagation pays the theory's per-assert cost.
                if self.timed_out() {
                    break;
                }
                let Some(var) = self.theory_variable(lit.atom) else {
                    continue;
                };
                if !self.active[var] {
                    continue;
                }
                match self.value[var] {
                    Some(v) if v == lit.value => {}
                    Some(_) => {
                        // The theory entails the opposite of the current value: learn
                        // ¬(reason ∧ current literal). The reason is needed *now*, so
                        // a deferred handle is resolved here.
                        let Some(mut core) = self.resolve_explanation(theory, explanation) else {
                            outcome = Ok(());
                            break;
                        };
                        core.push(TheoryLit {
                            atom: lit.atom,
                            value: !lit.value,
                        });
                        outcome = Err(Conflict {
                            clause: self.theory_conflict_clause(&core),
                            is_theory: true,
                        });
                        break;
                    }
                    None => {
                        // A deferred reason is *not* resolved here — that is the
                        // whole point of the handle. The variable is assigned with
                        // no stored reason clause and the handle recorded beside
                        // it; `Self::reason_for` materialises it only if conflict
                        // analysis reaches this literal.
                        let reason_clause = match &explanation {
                            TheoryExplanation::Eager(reason) => {
                                Some(self.theory_reason_clause(reason, lit))
                            }
                            TheoryExplanation::Lazy(_) => None,
                        };
                        let deferred = match explanation {
                            TheoryExplanation::Eager(_) => None,
                            TheoryExplanation::Lazy(handle) => Some(handle),
                        };
                        match self.assign(
                            theory,
                            var,
                            lit.value,
                            Cause::Implied,
                            reason_clause,
                            true,
                        ) {
                            Ok(()) => {}
                            Err(c) => {
                                outcome = Err(Conflict {
                                    clause: self.theory_conflict_clause(&c),
                                    is_theory: true,
                                });
                                break;
                            }
                        }
                        self.deferred_reason[var] = deferred;
                        self.theory_propagations += 1;
                        progress = true;
                    }
                }
            }
            queue.clear();
            self.prop_queue = queue;
            outcome?;
            if self.explanation_unresolved || self.timed_out() || !progress {
                return Ok(());
            }
        }
    }

    /// Maps a theory conflict core to the learned CNF conflict clause `¬⋀core` (every
    /// literal currently false, so it is the falsified clause to analyse).
    fn theory_conflict_clause(&self, core: &[TheoryLit]) -> Vec<Lit> {
        core.iter()
            .map(|l| Lit {
                var: self.theory_var_for_atom[l.atom],
                positive: !l.value,
            })
            .collect()
    }

    /// The reason clause for a theory propagation `reason ⊨ lit`, namely
    /// `¬(reason) ∨ lit`. Once every reason literal is asserted, this clause is unit
    /// and forces `lit` — the invariant [`Self::analyze_conflict`] relies on.
    fn theory_reason_clause(&self, reason: &[TheoryLit], lit: TheoryLit) -> Vec<Lit> {
        let mut clause: Vec<Lit> = reason
            .iter()
            .map(|l| Lit {
                var: self.theory_var_for_atom[l.atom],
                positive: !l.value,
            })
            .collect();
        clause.push(Lit {
            var: self.theory_var_for_atom[lit.atom],
            positive: lit.value,
        });
        clause
    }

    /// 1-UIP conflict analysis over the mixed (Boolean + theory) implication graph.
    /// Resolves the falsified `conflict` clause against the reason clauses of
    /// current-level literals (newest-first on the trail) until a single current-level
    /// literal — the first UIP — remains. Returns the asserting clause (UIP at index
    /// 0, lower-level literals after), the backjump level, and whether the clause is a
    /// pure theory lemma (resolved through theory clauses only).
    /// Returns `None` when a deferred theory explanation could not be resolved
    /// (ADR-1701): the caller then abandons the search as `Unknown`. It never
    /// returns the empty asserting clause for that case, which would be a wrong
    /// `unsat`.
    fn analyze_conflict<T: TheorySolver>(
        &mut self,
        theory: &mut T,
        conflict: &[Lit],
        seed_is_theory: bool,
    ) -> Option<(Vec<Lit>, usize, bool)> {
        let mut seen = vec![false; self.var_count];
        let mut lower: Vec<Lit> = Vec::new();
        let mut path_count = 0_usize;
        let mut pivot: Option<usize> = None;
        let mut index = self.trail.len();
        let current = self.decision_level;
        let mut all_theory = seed_is_theory;
        let mut clause: Vec<Lit> = conflict.to_vec();

        loop {
            for lit in &clause {
                let v = lit.var;
                if Some(v) == pivot || seen[v] || self.level[v] == 0 {
                    continue;
                }
                seen[v] = true;
                self.bump_var(v);
                if self.level[v] >= current {
                    path_count += 1;
                } else {
                    lower.push(*lit);
                }
            }

            let mut found = false;
            while index > 0 {
                index -= 1;
                if seen[self.trail[index].0] {
                    found = true;
                    break;
                }
            }
            if !found {
                // Implied at level 0: the empty asserting clause (UNSAT).
                return Some((Vec::new(), 0, all_theory));
            }

            let var = self.trail[index].0;
            seen[var] = false;
            path_count -= 1;
            pivot = Some(var);

            if path_count == 0 {
                let mut learned = Vec::with_capacity(lower.len() + 1);
                learned.push(self.true_literal(var).negate());
                learned.extend(lower);
                // Put the highest-level non-asserting literal at index 1, the
                // convention `proof_sat.rs`'s `analyze` follows, so the learned
                // clause's second watch is the last one a backjump undoes. The
                // returned backjump level is unchanged by the swap: it is the
                // maximum level over `learned[1..]` either way.
                if learned.len() >= 2 {
                    let mut best = 1;
                    for k in 2..learned.len() {
                        if self.level[learned[k].var] > self.level[learned[best].var] {
                            best = k;
                        }
                    }
                    learned.swap(1, best);
                }
                let backjump = Self::backjump_level(&self.level, &learned);
                return Some((learned, backjump, all_theory));
            }

            all_theory = all_theory && self.reason_theory[var];
            // Resolving against this literal is the *only* moment its reason is
            // needed, which is why a theory may hand the driver a handle instead
            // of the literals (ADR-1701).
            assert!(
                self.reason[var].is_some()
                    || self.reason_clause[var].is_some()
                    || self.deferred_reason[var].is_some(),
                "a current-level implied literal has a reason clause"
            );
            let Some(reason) = self.reason_for(theory, var) else {
                // The theory could not resolve a handle it emitted. Abandon the
                // search; never learn from a reason nobody can state.
                return None;
            };
            clause = reason;
        }
    }

    /// The backjump level: the second-highest decision level among the clause's
    /// literals (the asserting literal at index 0 sits at the highest level), or `0`
    /// for a unit asserting clause.
    fn backjump_level(level: &[usize], learned: &[Lit]) -> usize {
        learned
            .iter()
            .skip(1)
            .map(|lit| level[lit.var])
            .max()
            .unwrap_or(0)
    }

    /// Backjumps to `target_level`: pops every trail entry strictly above it,
    /// unassigning each variable and popping the theory once per decision crossed (it
    /// was pushed once per decision, keeping the push/pop stack in lockstep).
    fn backjump_to<T: TheorySolver>(&mut self, theory: &mut T, target_level: usize) {
        while let Some(&(var, _, _)) = self.trail.last() {
            if self.level[var] <= target_level {
                break;
            }
            let (var, _, cause) = self.trail.pop().expect("non-empty trail");
            self.value[var] = None;
            self.reason[var] = None;
            self.reason_theory[var] = false;
            self.reason_clause[var] = None;
            // A deferred explanation handle is dropped in the same step the
            // theory is popped past the level that justified it (ADR-1701), so a
            // handle can never outlive the theory state behind it.
            self.deferred_reason[var] = None;
            if cause == Cause::Decision {
                if self.collect_layer_stats {
                    let started = Instant::now();
                    theory.pop();
                    self.time_theory_push_pop += started.elapsed();
                } else {
                    theory.pop();
                }
            }
        }
        self.decision_level = target_level;
        // The two-watched-literal invariant survives a backjump untouched (a
        // watched literal only ever becomes *less* false), but the propagation
        // cursor must not point past the shortened trail, or the literals that
        // remain unpropagated below it would be skipped for good.
        self.qhead = self.qhead.min(self.trail.len());
    }

    /// The highest-activity unassigned variable, with deterministic lowest-index
    /// ties, or `None` when the assignment is total.
    fn pick_unassigned(&self) -> Option<usize> {
        let mut best = None;
        for var in 0..self.var_count {
            if !self.active[var] || self.value[var].is_some() {
                continue;
            }
            match best {
                None => best = Some(var),
                Some(current) if self.activity[var] > self.activity[current] => {
                    best = Some(var);
                }
                Some(_) => {}
            }
        }
        best
    }

    /// Bumps one variable's VSIDS activity, rescaling all activities by the same
    /// positive factor before they can overflow. Rescaling preserves ordering.
    fn bump_var(&mut self, var: usize) {
        self.activity[var] += self.var_inc;
        if self.activity[var] > VSIDS_RESCALE_LIMIT {
            for activity in &mut self.activity {
                *activity *= VSIDS_RESCALE;
            }
            self.var_inc *= VSIDS_RESCALE;
        }
    }

    /// Advances the VSIDS recency window after one analyzed conflict.
    fn decay_activity(&mut self) {
        self.var_inc /= VSIDS_DECAY;
    }

    /// Number of conflicts allowed in the current restart interval. Saturation
    /// turns unreachable arithmetic overflow into a delayed restart, never a
    /// spuriously early one.
    fn restart_limit(&self) -> usize {
        #[cfg(test)]
        let unit = self.restart_unit_override.unwrap_or(LUBY_UNIT);
        #[cfg(not(test))]
        let unit = LUBY_UNIT;
        usize::try_from(luby(self.restart_index))
            .unwrap_or(usize::MAX)
            .saturating_mul(unit)
    }

    /// Unit propagation interleaved with theory propagation to a joint fixpoint.
    /// Returns `Ok(())` early (not at fixpoint) when the deadline elapses so the
    /// caller's loop can turn it into [`Outcome::Unknown`].
    fn propagate<T: TheorySolver>(&mut self, theory: &mut T) -> Result<(), Conflict> {
        loop {
            if self.timed_out() {
                return Ok(());
            }
            if self.collect_layer_stats {
                let started = Instant::now();
                let outcome = self.unit_propagate(theory);
                self.time_boolean_propagate += started.elapsed();
                outcome?;
            } else {
                self.unit_propagate(theory)?;
            }
            let before = self.trail.len();
            self.theory_propagate(theory)?;
            if self.trail.len() == before {
                return Ok(());
            }
        }
    }

    /// Handles a conflict by 1-UIP analysis: learns the asserting clause, jumps
    /// non-chronologically to the backjump level, and enqueues the UIP literal as an
    /// implied assignment with the learned clause as its reason. Returns
    /// [`Learn::Unsat`] when the conflict is implied at level 0.
    fn learn_and_backjump<T: TheorySolver>(
        &mut self,
        theory: &mut T,
        conflict: &Conflict,
    ) -> Learn {
        if conflict.is_theory {
            self.theory_conflicts += 1;
        }
        let analyzed = if self.collect_layer_stats {
            let started = Instant::now();
            let result = self.analyze_conflict(theory, &conflict.clause, conflict.is_theory);
            self.time_conflict_analysis += started.elapsed();
            result
        } else {
            self.analyze_conflict(theory, &conflict.clause, conflict.is_theory)
        };
        let Some((learned, backjump, is_theory_lemma)) = analyzed else {
            return Learn::Abort;
        };
        self.decay_activity();
        self.conflicts_since_restart += 1;
        if learned.is_empty() {
            return Learn::Unsat;
        }
        self.backjump_to(theory, backjump);
        let uip = learned[0];
        // A multi-literal learned clause is its UIP's reason *by id*: it lives in
        // the clause database, so `Self::reason_for` reads it out of the arena on
        // the rare conflict-analysis path instead of cloning it here. A learned
        // unit is asserted at level zero and needs no reason at all.
        let reason: Option<Vec<Lit>> = None;
        let lbd = self.compute_lbd(&learned);
        let locked = learned.len() >= 2;
        let clause_id = self.alloc_clause(&learned);
        self.register_learned(lbd);
        // The backjump has already run, so `learned[0]` (the UIP) is unassigned
        // and every other literal is false at a level at or below the backjump
        // level. Watching slots 0 and 1 is therefore the correct assignment-aware
        // choice, and `learned[1]` is the deepest of the false literals by the
        // swap in `analyze_conflict` -- the same two-watch install
        // `proof_sat.rs` performs after its own backjump.
        self.attach_clause(clause_id);
        // Enqueue the UIP literal. Its theory assertion is consistent at the backjump
        // level (the asserting clause is an entailed resolvent), but a theory conflict
        // can still surface — re-analyse it. The learned clause is the UIP's reason,
        // a theory clause iff it is a theory lemma.
        let assigned = self.assign(
            theory,
            uip.var,
            uip.positive,
            Cause::Implied,
            reason,
            is_theory_lemma,
        );
        if locked {
            self.reason_clause[uip.var] = Some(clause_id);
        }
        if self.learned_live > self.reduce_budget() {
            self.reduce_db();
            self.reductions += 1;
        }
        match assigned {
            Ok(()) => Learn::Continue,
            Err(core) => self.learn_and_backjump(
                theory,
                &Conflict {
                    clause: self.theory_conflict_clause(&core),
                    is_theory: true,
                },
            ),
        }
    }

    /// Number of distinct decision levels represented by a learned clause.
    fn compute_lbd(&self, clause: &[Lit]) -> usize {
        let mut levels: Vec<usize> = clause.iter().map(|lit| self.level[lit.var]).collect();
        levels.sort_unstable();
        levels.dedup();
        levels.len()
    }

    /// Appends metadata for the learned clause just pushed into `clauses`.
    fn register_learned(&mut self, lbd: usize) {
        self.lbd.push(lbd);
        self.clause_activity.push(self.clause_increment);
        self.deleted.push(false);
        self.clause_increment += 1.0;
        self.learned_live += 1;
    }

    /// Current live learned-clause budget under the additive reduction schedule.
    fn reduce_budget(&self) -> usize {
        #[cfg(test)]
        let first = self.reduce_first_override.unwrap_or(REDUCE_FIRST);
        #[cfg(not(test))]
        let first = REDUCE_FIRST;
        first.saturating_add(REDUCE_INCREMENT.saturating_mul(self.reductions))
    }

    /// Which clauses are currently the reason for some assigned literal, indexed
    /// by clause id. Such a clause is **locked**: deleting it would corrupt the
    /// implication graph.
    ///
    /// Answered for every clause in one walk of `reason_clause` rather than by a
    /// per-clause scan, which would be quadratic in the search's size once
    /// propagation is fast enough to reach reduction on a large skeleton. The set
    /// of protected clauses is exactly the previous per-clause predicate's.
    ///
    /// The recorded reason ids are consulted rather than the clause's first
    /// literal: a clause can imply a literal other than its original UIP, so
    /// clause order is not evidence of what is locked.
    fn locked_clauses(&self) -> Vec<bool> {
        let mut locked = vec![false; self.headers.len()];
        for (var, reason) in self.reason_clause.iter().enumerate() {
            if self.value[var].is_some()
                && let Some(clause) = *reason
            {
                locked[clause] = true;
            }
        }
        locked
    }

    /// Tombstones the worst half of deletion-eligible learned clauses. Originals,
    /// glue clauses, and active reasons are retained. Ordering is total and
    /// deterministic: descending LBD, oldest activity, then newest slot.
    fn reduce_db(&mut self) {
        let locked = self.locked_clauses();
        let mut candidates: Vec<usize> = (self.num_original..self.headers.len())
            .filter(|&clause| {
                !self.deleted[clause] && self.lbd[clause] > GLUE_LBD && !locked[clause]
            })
            .collect();
        candidates.sort_by(|&left, &right| {
            self.lbd[right]
                .cmp(&self.lbd[left])
                .then_with(|| self.clause_activity[left].total_cmp(&self.clause_activity[right]))
                .then_with(|| right.cmp(&left))
        });
        let remove = candidates.len() / 2;
        for clause in candidates.into_iter().take(remove) {
            self.deleted[clause] = true;
            self.learned_live -= 1;
        }
        if remove > 0 {
            // No watch list may name a tombstoned clause.
            self.rebuild_watches();
        }
    }

    /// Runs the CDCL(T) search over the theory. Returns [`Outcome::Unsat`] on a
    /// refutation, [`Outcome::Sat`] on a Boolean- and theory-consistent total
    /// assignment (the theory is left in that state), or [`Outcome::Unknown`] on
    /// deadline.
    ///
    /// `pub` bench-only (see the type doc); reachable outside the crate only
    /// via [`crate::bench_internals`].
    ///
    /// Thin wrapper over [`Self::solve_inner`]: publishes [`TheoryLayerStats`]
    /// to [`last_theory_layer_stats`] on the way out when collection is
    /// enabled, so every early `return` inside the search loop has exactly
    /// one place recording the final snapshot.
    pub fn solve<T: TheorySolver>(&mut self, theory: &mut T) -> Outcome {
        let outcome = self.solve_inner(theory);
        if self.collect_layer_stats {
            let stats = self.theory_layer_stats(theory);
            LAST_THEORY_LAYER_STATS.with(|c| c.set(Some(stats)));
        }
        outcome
    }

    /// [`Self::theory_layer_stats`]-producing counterpart of
    /// [`crate::layers::BvLayerStats::from_solve_stats`]: lifts this search's
    /// accumulated stage timings and counters into the typed, named
    /// [`TheoryLayerStats`] a caller can compare or print, exactly as
    /// `BvLayerStats` lifts the `sat-bv` backend's counters.
    fn theory_layer_stats<T: TheorySolver>(&self, theory: &T) -> TheoryLayerStats {
        let engine = theory.engine_counters();
        TheoryLayerStats {
            boolean_propagate: self.time_boolean_propagate,
            theory_assert: self.time_theory_assert,
            theory_propagate: self.time_theory_propagate,
            theory_push_pop: self.time_theory_push_pop,
            conflict_analysis: self.time_conflict_analysis,
            theory_final_check: self.time_theory_final_check,
            theory_explain: self.time_theory_explain,
            #[allow(clippy::cast_possible_truncation)]
            final_checks: self.final_checks as u64,
            #[allow(clippy::cast_possible_truncation)] // Conflict/decision counts fit u64 in practice.
            theory_conflicts: self.theory_conflicts as u64,
            #[allow(clippy::cast_possible_truncation)]
            theory_propagations: self.theory_propagations as u64,
            #[allow(clippy::cast_possible_truncation)]
            decisions: self.decisions as u64,
            restarts: self.restarts(),
            // S4 wired `TheorySolver::engine_counters`; a theory that keeps no
            // feasibility engine still reports `None` here rather than zero.
            simplex_pivots: engine.map(|e| e.simplex_pivots),
            simplex_checks: engine.map(|e| e.simplex_checks),
            simplex_cold_restarts: engine.map(|e| e.simplex_cold_restarts),
            bound_retractions: engine.map(|e| e.bound_retractions),
            bound_assertions: engine.map(|e| e.bound_assertions),
            theory_propagations_offered: engine.map(|e| e.propagations),
            simplex_rows: engine.map(|e| e.simplex_rows),
            simplex_columns: engine.map(|e| e.simplex_columns),
        }
    }

    /// Runs [`TheorySolver::final_check`] at a total Boolean assignment and turns
    /// its answer into a search step (ADR-1701).
    ///
    /// The core of a final-check conflict is **not** required to name a
    /// current-decision-level literal — a complete check looks at the whole
    /// assignment, not at the literal that just arrived — so it cannot be handed
    /// straight to 1-UIP analysis, whose path counter assumes the trigger-literal
    /// invariant. This backjumps to the highest decision level the core names
    /// first. An all-level-0 core then makes 1-UIP derive the empty asserting
    /// clause, which is the correct `Unsat`.
    fn run_final_check<T: TheorySolver>(&mut self, theory: &mut T) -> FinalCheck {
        let outcome = if self.collect_layer_stats {
            let started = Instant::now();
            let outcome = theory.final_check();
            self.time_theory_final_check += started.elapsed();
            outcome
        } else {
            theory.final_check()
        };
        self.final_checks += 1;
        let explanation = match outcome {
            FinalCheckOutcome::Sat => return FinalCheck::Sat,
            FinalCheckOutcome::Unknown => return FinalCheck::Unknown,
            FinalCheckOutcome::Conflict(explanation) => explanation,
        };
        let Some(core) = self.resolve_explanation(theory, explanation) else {
            return FinalCheck::Unknown;
        };
        if core.is_empty() {
            // A conflict with no core names nothing to learn from; treating it as
            // the empty clause would be a wrong `unsat`.
            return FinalCheck::Unknown;
        }
        let clause = self.theory_conflict_clause(&core);
        let trigger_level = clause
            .iter()
            .map(|lit| self.level[lit.var])
            .max()
            .unwrap_or(0);
        if trigger_level < self.decision_level {
            self.backjump_to(theory, trigger_level);
        }
        let conflict = Conflict {
            clause,
            is_theory: true,
        };
        match self.learn_and_backjump(theory, &conflict) {
            Learn::Unsat => FinalCheck::Unsat,
            Learn::Abort => FinalCheck::Unknown,
            Learn::Continue => FinalCheck::Continue,
        }
    }

    fn solve_inner<T: TheorySolver>(&mut self, theory: &mut T) -> Outcome {
        loop {
            // Defense in depth against a non-monotone-theory livelock: bound the
            // main-loop iterations even with no deadline. Sound — `Unknown` is a
            // permitted verdict — never a wrong sat/unsat.
            if self.steps >= self.step_budget {
                self.step_budget_hit = true;
                return Outcome::Unknown;
            }
            self.steps += 1;
            if self.timed_out() {
                return Outcome::Unknown;
            }
            match self.propagate(theory) {
                Ok(()) => {}
                Err(conflict) => match self.learn_and_backjump(theory, &conflict) {
                    Learn::Unsat => return Outcome::Unsat,
                    Learn::Abort => return Outcome::Unknown,
                    Learn::Continue => continue,
                },
            }
            if self.explanation_unresolved {
                return Outcome::Unknown;
            }
            if self.timed_out() {
                return Outcome::Unknown;
            }
            if self.decision_level > 0 && self.conflicts_since_restart >= self.restart_limit() {
                self.backjump_to(theory, 0);
                self.conflicts_since_restart = 0;
                self.restart_index += 1;
                continue;
            }
            match self.pick_unassigned() {
                // A *total* assignment of the active variables: the one moment a
                // theory's complete check is due (ADR-1701). A theory keeping the
                // trait default answers `Sat` here, so this is byte-identical to
                // the previous unconditional `return Outcome::Sat`.
                None => match self.run_final_check(theory) {
                    FinalCheck::Sat => return Outcome::Sat,
                    FinalCheck::Unknown => return Outcome::Unknown,
                    FinalCheck::Unsat => return Outcome::Unsat,
                    FinalCheck::Continue => {}
                },
                Some(var) => {
                    self.decision_level += 1;
                    self.decisions += 1;
                    if self.collect_layer_stats {
                        let started = Instant::now();
                        theory.push();
                        self.time_theory_push_pop += started.elapsed();
                    } else {
                        theory.push();
                    }
                    let polarity = self.saved_phase[var];
                    if let Err(core) =
                        self.assign(theory, var, polarity, Cause::Decision, None, false)
                    {
                        let conflict = Conflict {
                            clause: self.theory_conflict_clause(&core),
                            is_theory: true,
                        };
                        match self.learn_and_backjump(theory, &conflict) {
                            Learn::Unsat => return Outcome::Unsat,
                            Learn::Abort => return Outcome::Unknown,
                            Learn::Continue => {}
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod termination_tests {
    //! Termination + soundness of the generic [`CdclT`] driver under an
    //! **adversarial, non-monotone** theory (DEBT 1 of the default-on verification
    //! debt paydown).
    //!
    //! [`MockTheory`] is a deliberately hostile [`TheorySolver`]: its *truth* is a
    //! fixed set of forbidden cubes (a partial assignment the theory has no model
    //! for — so `¬cube` is a valid theory lemma), but its *reporting* is
    //! non-monotone — on a **partial** assignment it may report a contained cube,
    //! skip one it could report (miss), flip-flop, or report a superset core,
    //! mirroring how the real [`crate::string_theory::StringTheory`] re-runs an
    //! incomplete refuter per assert. It is **complete on total assignments** (when
    //! every atom is assigned it always reports a contained cube), and it always
    //! folds the current-decision-level trigger literal into the core — exactly the
    //! `c9d332c1` trigger-literal invariant the driver's 1-UIP analysis relies on.
    //!
    //! The property: over thousands of random instances the driver must (a)
    //! **terminate** without tripping the step budget (no livelock), and (b) return
    //! a verdict that matches an independent brute-force over the Boolean skeleton ∧
    //! the forbidden-cube semantics — a wrong `Sat`/`Unsat` is a hard failure.

    use super::{Cause, CdclT, Lit, Outcome, luby};
    use crate::euf_egraph::{TheoryLit, TheoryProp, TheorySolver};

    /// A deterministic linear-congruential PRNG (MMIX constants) — the house
    /// convention; no clock, no entropy, fully reproducible per seed.
    struct Lcg(u64);

    impl Lcg {
        fn new(seed: u64) -> Self {
            Lcg(seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407)
                .wrapping_add(0x9E37_79B9_7F4A_7C15))
        }
        fn next_u64(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            self.0
        }
        fn below(&mut self, n: usize) -> usize {
            usize::try_from(self.next_u64() % (n as u64)).expect("modulus fits usize")
        }
        fn coin(&mut self) -> bool {
            self.next_u64() & 1 == 1
        }
    }

    /// How the mock decides, on a **partial** assignment, whether to report a
    /// contained forbidden cube. All variants stay sound (every reported core is a
    /// genuine ¬cube lemma); they differ only in *when* they fire, so the driver
    /// meets a hostile, non-monotone conflict schedule.
    #[derive(Clone, Copy)]
    enum Mode {
        /// Report on every partial assert where a cube is contained (eager).
        Always,
        /// Never report on a partial assignment — only at a total one (maximally
        /// late; the driver reaches full models before the theory ever speaks).
        OnlyTotal,
        /// Report only on every `k`-th qualifying assert (periodic miss).
        Periodic(u64),
        /// Alternate report / skip on successive qualifying asserts (flip-flop).
        FlipFlop,
    }

    /// The adversarial non-monotone theory. `forbidden` fixes its semantics; the
    /// reporting schedule (`mode`) is hostile but never unsound.
    struct MockTheory {
        n: usize,
        forbidden: Vec<Vec<(usize, bool)>>,
        mode: Mode,
        /// Whether the core should be padded to a superset of a genuine cube (still
        /// sound). Independent of `mode`.
        report_superset: bool,
        /// Per atom: currently-asserted value (`None` if unassigned).
        assigned: Vec<Option<bool>>,
        /// Number of atoms currently assigned (for the total-assignment test).
        assigned_count: usize,
        /// Atoms assigned since the start, in order — the backtrack log.
        assigned_log: Vec<usize>,
        /// Backtrack trail: per `push`, the `assigned_log` length.
        trail: Vec<usize>,
        /// Count of qualifying (cube-contained) partial asserts, driving the
        /// periodic / flip-flop schedules.
        qualifying: u64,
    }

    impl MockTheory {
        fn new(n: usize, forbidden: Vec<Vec<(usize, bool)>>, mode: Mode, superset: bool) -> Self {
            Self {
                n,
                forbidden,
                mode,
                report_superset: superset,
                assigned: vec![None; n],
                assigned_count: 0,
                assigned_log: Vec::new(),
                trail: Vec::new(),
                qualifying: 0,
            }
        }

        /// Whether every literal of `cube` is currently asserted with the matching
        /// value (the cube is contained in the current assignment).
        fn contains_cube(&self, cube: &[(usize, bool)]) -> bool {
            cube.iter().all(|&(a, v)| self.assigned[a] == Some(v))
        }

        /// The first contained forbidden cube, if any.
        fn contained_cube(&self) -> Option<&Vec<(usize, bool)>> {
            self.forbidden.iter().find(|c| self.contains_cube(c))
        }

        /// Builds a genuine theory-conflict core from `cube`: its literals, plus (in
        /// superset mode) every currently-asserted literal, plus the current-level
        /// `trigger` literal (the `c9d332c1` invariant). Every literal is genuinely
        /// asserted, so `¬core` is entailed by `¬cube` — a sound lemma.
        fn core_from(&self, cube: &[(usize, bool)], trigger: (usize, bool)) -> Vec<TheoryLit> {
            let mut core: Vec<TheoryLit> = Vec::new();
            let push_lit = |core: &mut Vec<TheoryLit>, atom: usize, value: bool| {
                if !core.iter().any(|l| l.atom == atom) {
                    core.push(TheoryLit { atom, value });
                }
            };
            for &(a, v) in cube {
                push_lit(&mut core, a, v);
            }
            if self.report_superset {
                for &a in &self.assigned_log {
                    if let Some(v) = self.assigned[a] {
                        push_lit(&mut core, a, v);
                    }
                }
            }
            // Always carry the just-asserted current-level literal, so the driver's
            // 1-UIP analysis always finds a current-level literal to resolve on.
            push_lit(&mut core, trigger.0, trigger.1);
            core
        }
    }

    impl TheorySolver for MockTheory {
        fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
            if self.assigned[atom].is_none() {
                self.assigned[atom] = Some(value);
                self.assigned_count += 1;
                self.assigned_log.push(atom);
            }
            let trigger = (atom, value);
            // A total assignment: the mock is COMPLETE here — always report a
            // contained cube, so the driver never accepts a theory-inconsistent model.
            let total = self.assigned_count == self.n;
            let Some(cube) = self.contained_cube().cloned() else {
                return Ok(());
            };
            if total {
                return Err(self.core_from(&cube, trigger));
            }
            // Partial: hostile, non-monotone schedule — but every fired core is sound.
            self.qualifying += 1;
            let fire = match self.mode {
                Mode::Always => true,
                Mode::OnlyTotal => false,
                Mode::Periodic(k) => self.qualifying.is_multiple_of(k),
                Mode::FlipFlop => self.qualifying.is_multiple_of(2),
            };
            if fire {
                Err(self.core_from(&cube, trigger))
            } else {
                Ok(())
            }
        }

        fn push(&mut self) {
            self.trail.push(self.assigned_log.len());
        }

        fn pop(&mut self) {
            if let Some(mark) = self.trail.pop() {
                while self.assigned_log.len() > mark {
                    if let Some(atom) = self.assigned_log.pop() {
                        self.assigned[atom] = None;
                        self.assigned_count -= 1;
                    }
                }
            }
        }

        fn propagate(&self) -> Vec<TheoryProp> {
            // Like the real StringTheory: no theory propagation this model.
            Vec::new()
        }
    }

    /// A generated instance: `n` atoms (all driver variables are theory atoms),
    /// CNF `clauses` over them, and the theory's forbidden cubes.
    struct Instance {
        n: usize,
        clauses: Vec<Vec<Lit>>,
        forbidden: Vec<Vec<(usize, bool)>>,
    }

    fn gen_instance(rng: &mut Lcg) -> Instance {
        let n = 1 + rng.below(6); // 1..=6 atoms
        let m = rng.below(2 * n + 1); // 0..=2n clauses
        let mut clauses = Vec::with_capacity(m);
        for _ in 0..m {
            let width = 1 + rng.below(3); // 1..=3 literals
            let mut clause = Vec::with_capacity(width);
            for _ in 0..width {
                let var = rng.below(n);
                let positive = rng.coin();
                if !clause.iter().any(|l: &Lit| l.var == var) {
                    clause.push(Lit { var, positive });
                }
            }
            clauses.push(clause);
        }
        let f = rng.below(n + 1); // 0..=n forbidden cubes
        let mut forbidden = Vec::with_capacity(f);
        for _ in 0..f {
            let width = 1 + rng.below(3); // 1..=3 literals
            let mut cube: Vec<(usize, bool)> = Vec::with_capacity(width);
            for _ in 0..width {
                let atom = rng.below(n);
                let value = rng.coin();
                // A cube with contradictory literals on one atom can never be
                // contained; drop the duplicate to keep cubes meaningful.
                if !cube.iter().any(|&(a, _)| a == atom) {
                    cube.push((atom, value));
                }
            }
            if !cube.is_empty() {
                forbidden.push(cube);
            }
        }
        Instance {
            n,
            clauses,
            forbidden,
        }
    }

    /// Whether `assignment` (bit `i` = value of atom `i`) satisfies every clause.
    fn sat_clauses(clauses: &[Vec<Lit>], assignment: u32) -> bool {
        clauses.iter().all(|clause| {
            clause
                .iter()
                .any(|l| ((assignment >> l.var) & 1 == 1) == l.positive)
        })
    }

    /// Whether `assignment` contains no forbidden cube (theory-consistent).
    fn theory_consistent(forbidden: &[Vec<(usize, bool)>], assignment: u32) -> bool {
        !forbidden
            .iter()
            .any(|cube| cube.iter().all(|&(a, v)| ((assignment >> a) & 1 == 1) == v))
    }

    /// Independent brute force over all `2^n` total assignments: `true` iff some
    /// assignment satisfies every clause and avoids every forbidden cube.
    fn brute_force_sat(inst: &Instance) -> bool {
        (0u32..(1u32 << inst.n))
            .any(|a| sat_clauses(&inst.clauses, a) && theory_consistent(&inst.forbidden, a))
    }

    /// Drives one instance through [`CdclT`] under `mode`/`superset`, with a tight
    /// step budget so a livelock trips it deterministically rather than hanging.
    fn run_once(inst: &Instance, mode: Mode, superset: bool) -> (Outcome, CdclT) {
        // A step ceiling far above any legitimate run on <=6 atoms (whose full CDCL
        // search is at most a few thousand steps) but finite — a true livelock trips
        // it and the test asserts it was NOT tripped.
        const TEST_STEP_BUDGET: usize = 200_000;
        let mut solver = CdclT::new(inst.n, inst.n, inst.clauses.clone(), None)
            .with_step_budget(TEST_STEP_BUDGET);
        let mut theory = MockTheory::new(inst.n, inst.forbidden.clone(), mode, superset);
        let outcome = solver.solve(&mut theory);
        (outcome, solver)
    }

    #[test]
    fn non_monotone_theory_terminates_and_is_sound() {
        // Every mode × superset-flag combination, over a large random sweep.
        let modes = [
            Mode::Always,
            Mode::OnlyTotal,
            Mode::Periodic(2),
            Mode::Periodic(3),
            Mode::FlipFlop,
        ];
        let mut runs = 0u64;
        let mut sat = 0u64;
        let mut unsat = 0u64;
        // 2000 base instances × 10 (mode × superset) schedules = 20_000 driver runs.
        for seed in 0..2000u64 {
            let mut rng = Lcg::new(seed);
            let inst = gen_instance(&mut rng);
            let truth = brute_force_sat(&inst);
            for &mode in &modes {
                for &superset in &[false, true] {
                    let (outcome, solver) = run_once(&inst, mode, superset);
                    runs += 1;

                    // (1) Termination: the driver must decide by its own logic, never
                    // by exhausting the step budget — a trip is a livelock.
                    assert!(
                        !solver.step_budget_hit(),
                        "LIVELOCK seed={seed} n={} mode-idx step-budget exhausted \
                         (took {} steps) — the non-monotone driver did not terminate",
                        inst.n,
                        solver.steps,
                    );
                    // With no deadline and the budget untripped, `Unknown` is impossible.
                    assert_ne!(
                        outcome,
                        Outcome::Unknown,
                        "seed={seed}: Unknown without a deadline or budget trip",
                    );

                    match outcome {
                        Outcome::Unsat => {
                            // (2a) Soundness of UNSAT: brute force must agree no model
                            // exists.
                            assert!(
                                !truth,
                                "WRONG UNSAT seed={seed} n={}: driver said Unsat but a \
                                 skeleton+theory model exists",
                                inst.n,
                            );
                            unsat += 1;
                        }
                        Outcome::Sat => {
                            // (2b) Soundness of SAT: read the driver's assignment and
                            // confirm it satisfies the skeleton AND avoids every
                            // forbidden cube (a genuine model), independent of the mock.
                            let mut assignment = 0u32;
                            for v in 0..inst.n {
                                let val = solver
                                    .value(v)
                                    .expect("a Sat verdict assigns every variable");
                                if val {
                                    assignment |= 1 << v;
                                }
                            }
                            assert!(
                                sat_clauses(&inst.clauses, assignment),
                                "WRONG SAT seed={seed}: model violates the skeleton",
                            );
                            assert!(
                                theory_consistent(&inst.forbidden, assignment),
                                "WRONG SAT seed={seed}: model contains a forbidden cube \
                                 (theory-inconsistent)",
                            );
                            // And it agrees with the brute-force existence verdict.
                            assert!(truth, "seed={seed}: driver Sat but brute force UNSAT");
                            sat += 1;
                        }
                        Outcome::Unknown => unreachable!("ruled out above"),
                    }
                }
            }
        }
        eprintln!(
            "cdclt non-monotone termination: runs={runs} sat={sat} unsat={unsat} \
             (all terminated within the step budget; no wrong verdicts)"
        );
        assert!(
            sat > 0 && unsat > 0,
            "degenerate sweep: sat={sat} unsat={unsat} — expected a mix",
        );
    }

    /// A pointed regression for the exact hazard DEBT 1 names: a mock that reports
    /// the **same** conflict on repeated queries (here, on every qualifying assert)
    /// must not cause the driver to re-learn/spin — it terminates with the correct
    /// verdict. The forbidden cube `{a=true}` forces `a=false`; the clause `(a)`
    /// then makes the instance UNSAT, reached without livelock.
    #[test]
    fn repeated_same_conflict_does_not_livelock() {
        let inst = Instance {
            n: 2,
            clauses: vec![
                vec![Lit {
                    var: 0,
                    positive: true,
                }], // a must be true
            ],
            forbidden: vec![vec![(0, true)]], // but a=true is forbidden
        };
        let (outcome, solver) = run_once(&inst, Mode::Always, false);
        assert!(
            !solver.step_budget_hit(),
            "livelocked on a repeated conflict"
        );
        assert_eq!(outcome, Outcome::Unsat, "a ∧ ¬a-forbidden is UNSAT");
        assert!(!brute_force_sat(&inst), "brute force agrees: UNSAT");
    }

    #[test]
    fn vsids_bumps_conflict_vars_and_reorders_decisions_deterministically() {
        fn run() -> (Vec<f64>, Vec<Lit>) {
            // A conflict over four purely Boolean variables: the analysis never
            // reaches the theory, but the signature takes one (ADR-1701).
            struct NoTheory;
            impl TheorySolver for NoTheory {
                fn assert(&mut self, _atom: usize, _value: bool) -> Result<(), Vec<TheoryLit>> {
                    Ok(())
                }
                fn push(&mut self) {}
                fn pop(&mut self) {}
                fn propagate(&self) -> Vec<TheoryProp> {
                    Vec::new()
                }
            }
            let mut solver = CdclT::new(4, 0, Vec::new(), None);
            solver.decision_level = 1;
            solver.value[0] = Some(true);
            solver.level[0] = 1;
            solver.trail.push((0, true, Cause::Decision));
            solver.value[1] = Some(true);
            solver.level[1] = 1;
            solver.reason[1] = Some(vec![
                Lit {
                    var: 0,
                    positive: false,
                },
                Lit {
                    var: 1,
                    positive: true,
                },
            ]);
            solver.trail.push((1, true, Cause::Implied));
            let conflict = vec![
                Lit {
                    var: 0,
                    positive: false,
                },
                Lit {
                    var: 1,
                    positive: false,
                },
            ];
            let (learned, _, _) = solver
                .analyze_conflict(&mut NoTheory, &conflict, false)
                .expect("a purely Boolean analysis never defers an explanation");
            (solver.activity, learned)
        }

        let (activity, learned) = run();
        assert!(activity[0] > 0.0 && activity[1] > 0.0);
        assert!(activity[2] <= 0.0);
        assert!(activity[3] <= 0.0);
        assert_eq!(
            learned,
            vec![Lit {
                var: 0,
                positive: false,
            }]
        );

        let mut picker = CdclT::new(4, 0, Vec::new(), None);
        picker.bump_var(2);
        assert_eq!(picker.pick_unassigned(), Some(2));
        let plain = CdclT::new(4, 0, Vec::new(), None);
        assert_eq!(plain.pick_unassigned(), Some(0));

        let (activity_again, learned_again) = run();
        assert_eq!(activity, activity_again);
        assert_eq!(learned, learned_again);
    }

    #[test]
    fn phase_saving_survives_backtracking_and_preserves_true_first_default() {
        struct NoTheory;
        impl TheorySolver for NoTheory {
            fn assert(&mut self, _atom: usize, _value: bool) -> Result<(), Vec<TheoryLit>> {
                Ok(())
            }

            fn push(&mut self) {}

            fn pop(&mut self) {}

            fn propagate(&self) -> Vec<TheoryProp> {
                Vec::new()
            }
        }

        let mut theory = NoTheory;
        let mut solver = CdclT::new(3, 0, Vec::new(), None);
        assert_eq!(solver.saved_phase, vec![true, true, true]);

        solver.decision_level = 1;
        solver
            .assign(&mut theory, 0, false, Cause::Decision, None, false)
            .expect("pure Boolean assignment cannot conflict");
        solver
            .assign(&mut theory, 1, false, Cause::Implied, None, false)
            .expect("pure Boolean propagation cannot conflict");
        assert!(!solver.saved_phase[0]);
        assert!(!solver.saved_phase[1]);

        solver.backjump_to(&mut theory, 0);
        assert_eq!(solver.value[0], None);
        assert!(!solver.saved_phase[0]);
        assert!(solver.saved_phase[2]);
    }

    fn pigeonhole(pigeons: usize, holes: usize) -> (usize, Vec<Vec<Lit>>) {
        let variable = |pigeon: usize, hole: usize| pigeon * holes + hole;
        let mut clauses = Vec::new();
        for pigeon in 0..pigeons {
            clauses.push(
                (0..holes)
                    .map(|hole| Lit {
                        var: variable(pigeon, hole),
                        positive: true,
                    })
                    .collect(),
            );
            for left in 0..holes {
                for right in (left + 1)..holes {
                    clauses.push(vec![
                        Lit {
                            var: variable(pigeon, left),
                            positive: false,
                        },
                        Lit {
                            var: variable(pigeon, right),
                            positive: false,
                        },
                    ]);
                }
            }
        }
        for hole in 0..holes {
            for left in 0..pigeons {
                for right in (left + 1)..pigeons {
                    clauses.push(vec![
                        Lit {
                            var: variable(left, hole),
                            positive: false,
                        },
                        Lit {
                            var: variable(right, hole),
                            positive: false,
                        },
                    ]);
                }
            }
        }
        (pigeons * holes, clauses)
    }

    #[test]
    fn luby_restarts_fire_without_changing_verdict_or_theory_balance() {
        struct DepthTheory {
            depth: usize,
        }
        impl TheorySolver for DepthTheory {
            fn assert(&mut self, _atom: usize, _value: bool) -> Result<(), Vec<TheoryLit>> {
                Ok(())
            }

            fn push(&mut self) {
                self.depth += 1;
            }

            fn pop(&mut self) {
                self.depth = self.depth.checked_sub(1).expect("balanced theory pop");
            }

            fn propagate(&self) -> Vec<TheoryProp> {
                Vec::new()
            }
        }

        let (variables, clauses) = pigeonhole(5, 4);
        let run = |restart_unit| {
            let mut solver =
                CdclT::new(variables, 0, clauses.clone(), None).with_restart_unit(restart_unit);
            let mut theory = DepthTheory { depth: 0 };
            let outcome = solver.solve(&mut theory);
            (outcome, solver.restarts(), theory.depth)
        };

        let baseline = run(usize::MAX);
        assert_eq!(baseline, (Outcome::Unsat, 0, 0));
        let restarted = run(1);
        assert_eq!(restarted.0, baseline.0);
        assert!(restarted.1 > 0, "the lowered Luby schedule must restart");
        assert_eq!(restarted.2, 0, "restart must balance theory push/pop");
        assert_eq!(
            restarted,
            run(1),
            "restart trajectory must be deterministic"
        );
    }

    #[test]
    fn luby_sequence_matches_reluctant_doubling_prefix() {
        let actual: Vec<u64> = (1..=15).map(luby).collect();
        assert_eq!(actual, vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]);
    }

    #[test]
    fn lbd_reduction_fires_and_matches_never_delete_baseline() {
        struct NoTheory;
        impl TheorySolver for NoTheory {
            fn assert(&mut self, _atom: usize, _value: bool) -> Result<(), Vec<TheoryLit>> {
                Ok(())
            }

            fn push(&mut self) {}

            fn pop(&mut self) {}

            fn propagate(&self) -> Vec<TheoryProp> {
                Vec::new()
            }
        }

        let (variables, clauses) = pigeonhole(7, 6);
        let run = |first| {
            let mut solver = CdclT::new(variables, 0, clauses.clone(), None)
                .with_reduce_first(first)
                .with_restart_unit(usize::MAX);
            let outcome = solver.solve(&mut NoTheory);
            (
                outcome,
                solver.reductions(),
                solver.deleted_learned(),
                solver.no_deleted_active_reason(),
            )
        };

        let baseline = run(usize::MAX);
        assert_eq!(baseline.0, Outcome::Unsat);
        assert_eq!(baseline.1, 0);
        assert_eq!(baseline.2, 0);
        let reduced = run(3);
        assert_eq!(reduced.0, baseline.0);
        assert!(reduced.1 > 0, "the lowered reduction budget must fire");
        assert!(reduced.2 > 0, "reduction must tombstone learned clauses");
        assert!(reduced.3, "a tombstoned clause remained an active reason");
        assert_eq!(
            reduced,
            run(3),
            "reduction trajectory must be deterministic"
        );
    }

    #[test]
    fn reduction_protects_glue_and_locked_clauses() {
        let mut solver = CdclT::new(4, 0, Vec::new(), None);
        for (var, distance) in [(0, 2), (1, 5), (2, 4), (3, 3)] {
            // Clause 1's locked literal is deliberately not its first literal in
            // this fixture: lock protection follows the implication graph, not
            // clause order.
            let literals = if var == 1 {
                vec![
                    Lit {
                        var: 0,
                        positive: false,
                    },
                    Lit {
                        var,
                        positive: true,
                    },
                ]
            } else {
                vec![Lit {
                    var,
                    positive: true,
                }]
            };
            solver.alloc_clause(&literals);
            solver.register_learned(distance);
        }
        solver.value[1] = Some(true);
        solver.reason_clause[1] = Some(1);

        solver.reduce_db();

        assert!(!solver.deleted[0], "LBD-2 glue clause must be permanent");
        assert!(!solver.deleted[1], "locked reason clause must be retained");
        assert!(solver.deleted[2], "worst eligible clause should be removed");
        assert!(!solver.deleted[3], "only the worst half should be removed");
    }

    #[test]
    fn permanent_clause_activates_reserved_variable_and_resumes_search() {
        struct NoTheory;
        impl TheorySolver for NoTheory {
            fn assert(&mut self, _atom: usize, _value: bool) -> Result<(), Vec<TheoryLit>> {
                Ok(())
            }

            fn push(&mut self) {}

            fn pop(&mut self) {}

            fn propagate(&self) -> Vec<TheoryProp> {
                Vec::new()
            }
        }

        let mut solver = CdclT::new(2, 0, Vec::new(), None).with_inactive_variables(&[1]);
        assert_eq!(solver.solve(&mut NoTheory), Outcome::Sat);
        assert_eq!(solver.value(0), Some(true));
        assert_eq!(solver.value(1), None);

        solver.add_permanent_clause(vec![Lit {
            var: 1,
            positive: false,
        }]);
        assert_eq!(solver.solve(&mut NoTheory), Outcome::Sat);
        assert_eq!(solver.value(0), Some(true));
        assert_eq!(solver.value(1), Some(false));

        solver.add_permanent_clause(vec![
            Lit {
                var: 0,
                positive: false,
            },
            Lit {
                var: 1,
                positive: true,
            },
        ]);
        assert_eq!(solver.solve(&mut NoTheory), Outcome::Sat);
        assert_eq!(solver.value(0), Some(false));
        assert_eq!(solver.value(1), Some(false));
    }

    #[test]
    fn root_backtrack_retains_database_and_allows_resumed_insertion() {
        #[derive(Default)]
        struct DepthTheory(usize);
        impl TheorySolver for DepthTheory {
            fn assert(&mut self, _atom: usize, _value: bool) -> Result<(), Vec<TheoryLit>> {
                Ok(())
            }

            fn push(&mut self) {
                self.0 += 1;
            }

            fn pop(&mut self) {
                self.0 -= 1;
            }

            fn propagate(&self) -> Vec<TheoryProp> {
                Vec::new()
            }
        }

        let mut theory = DepthTheory::default();
        let mut solver = CdclT::new(2, 0, Vec::new(), None);
        assert_eq!(solver.solve(&mut theory), Outcome::Sat);
        assert_eq!(theory.0, 2);
        assert_eq!(solver.value(0), Some(true));
        assert_eq!(solver.value(1), Some(true));

        solver.backtrack_to_root(&mut theory);
        assert_eq!(theory.0, 0);
        assert_eq!(solver.value(0), None);
        assert_eq!(solver.value(1), None);

        solver.add_permanent_clause(vec![Lit {
            var: 1,
            positive: false,
        }]);
        assert_eq!(solver.solve(&mut theory), Outcome::Sat);
        assert_eq!(solver.value(1), Some(false));
    }

    #[test]
    fn inactive_theory_propagation_waits_for_activation() {
        struct ReservedPropagation;
        impl TheorySolver for ReservedPropagation {
            fn assert(&mut self, _atom: usize, _value: bool) -> Result<(), Vec<TheoryLit>> {
                Ok(())
            }

            fn push(&mut self) {}

            fn pop(&mut self) {}

            fn propagate(&self) -> Vec<TheoryProp> {
                vec![TheoryProp {
                    lit: TheoryLit {
                        atom: 1,
                        value: true,
                    },
                    reason: Vec::new(),
                }]
            }
        }

        let clauses = vec![vec![Lit {
            var: 0,
            positive: true,
        }]];
        let mut solver = CdclT::new(2, 2, clauses, None).with_inactive_variables(&[1]);
        let mut theory = ReservedPropagation;
        assert_eq!(solver.solve(&mut theory), Outcome::Sat);
        assert_eq!(solver.value(1), None);

        solver.add_permanent_clause(vec![Lit {
            var: 1,
            positive: false,
        }]);
        assert_eq!(solver.solve(&mut theory), Outcome::Unsat);
    }

    #[test]
    fn dynamic_theory_atom_after_boolean_auxiliary_maps_conflicts() {
        #[derive(Default)]
        struct DynamicTheory {
            assigned: Vec<(usize, bool)>,
        }

        impl TheorySolver for DynamicTheory {
            fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
                self.assigned.push((atom, value));
                Ok(())
            }

            fn push(&mut self) {}

            fn pop(&mut self) {}

            fn propagate(&self) -> Vec<TheoryProp> {
                vec![TheoryProp {
                    lit: TheoryLit {
                        atom: 1,
                        value: true,
                    },
                    reason: Vec::new(),
                }]
            }
        }

        let clauses = vec![
            vec![Lit {
                var: 0,
                positive: true,
            }],
            vec![Lit {
                var: 1,
                positive: true,
            }],
        ];
        let mut solver = CdclT::new(2, 1, clauses, None);
        let mut theory = DynamicTheory::default();
        assert_eq!(solver.solve(&mut theory), Outcome::Sat);

        let (variable, atom) = solver.add_theory_variable();
        assert_eq!((variable, atom), (2, 1));
        assert_eq!(solver.theory_variable(atom), Some(variable));
        solver.add_permanent_clause(vec![Lit {
            var: variable,
            positive: false,
        }]);

        assert_eq!(solver.solve(&mut theory), Outcome::Unsat);
        assert!(theory.assigned.contains(&(1, false)));
    }
}

#[cfg(test)]
mod adr1701_tests {
    //! Adversarial coverage for the four capabilities
    //! [ADR-1701](../../../docs/research/09-decisions/adr-1701-the-theory-interface-gains-final-check-a-driver-owned-queue-lazy-explanation-and-dynamic-atoms.md)
    //! added to [`TheorySolver`]: a complete check at a total assignment, a
    //! driver-owned propagation queue, deferred explanation handles, and
    //! dynamic atom registration.
    //!
    //! Every mock here is hostile in the specific way the corresponding hook
    //! has to survive: a theory that accepts every `assert` and only refutes
    //! the *complete* assignment; a theory that fails loudly if the driver ever
    //! hands it a queue it did not drain; a theory that counts how often the
    //! driver actually needed a reason; and a theory that grows its atom set
    //! mid-search and then conflicts on the atom it grew.

    use super::{CdclT, Lit, Outcome};
    use crate::euf_egraph::{
        ExplanationId, FinalCheckOutcome, PropagationQueue, TheoryExplanation, TheoryLit,
        TheoryProp, TheorySolver,
    };

    /// A backtrackable record of what the search has asserted, shared by the
    /// mocks below.
    #[derive(Default)]
    struct Trail {
        assigned: Vec<Option<bool>>,
        log: Vec<usize>,
        scopes: Vec<usize>,
    }

    impl Trail {
        fn new(atoms: usize) -> Self {
            Self {
                assigned: vec![None; atoms],
                log: Vec::new(),
                scopes: Vec::new(),
            }
        }

        fn set(&mut self, atom: usize, value: bool) {
            if atom >= self.assigned.len() {
                self.assigned.resize(atom + 1, None);
            }
            if self.assigned[atom].is_none() {
                self.log.push(atom);
            }
            self.assigned[atom] = Some(value);
        }

        fn push(&mut self) {
            self.scopes.push(self.log.len());
        }

        fn pop(&mut self) {
            let Some(mark) = self.scopes.pop() else {
                return;
            };
            while self.log.len() > mark {
                let atom = self.log.pop().expect("non-empty above the mark");
                self.assigned[atom] = None;
            }
        }

        fn value(&self, atom: usize) -> Option<bool> {
            self.assigned.get(atom).copied().flatten()
        }
    }

    // -----------------------------------------------------------------------
    // (a) final check
    // -----------------------------------------------------------------------

    /// Accepts **every** `assert` and refutes at [`TheorySolver::final_check`].
    /// Its truth is `forbid_all` ? "no total assignment is consistent" :
    /// "not both atom 0 and atom 1 true" — neither of which any single assert
    /// can detect, which is exactly the separation `final_check` exists for.
    struct FinalCheckOnly {
        trail: Trail,
        forbid_all: bool,
        final_checks: usize,
        accepted: Option<Vec<Option<bool>>>,
    }

    impl FinalCheckOnly {
        fn new(atoms: usize, forbid_all: bool) -> Self {
            Self {
                trail: Trail::new(atoms),
                forbid_all,
                final_checks: 0,
                accepted: None,
            }
        }
    }

    impl TheorySolver for FinalCheckOnly {
        fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
            self.trail.set(atom, value);
            Ok(())
        }
        fn push(&mut self) {
            self.trail.push();
        }
        fn pop(&mut self) {
            self.trail.pop();
        }
        fn propagate(&self) -> Vec<TheoryProp> {
            Vec::new()
        }
        fn final_check(&mut self) -> FinalCheckOutcome {
            self.final_checks += 1;
            if self.forbid_all {
                let core = self
                    .trail
                    .log
                    .iter()
                    .map(|&atom| TheoryLit {
                        atom,
                        value: self.trail.value(atom).expect("logged atoms are assigned"),
                    })
                    .collect::<Vec<_>>();
                return FinalCheckOutcome::Conflict(TheoryExplanation::Eager(core));
            }
            if self.trail.value(0) == Some(true) && self.trail.value(1) == Some(true) {
                return FinalCheckOutcome::Conflict(TheoryExplanation::Eager(vec![
                    TheoryLit {
                        atom: 0,
                        value: true,
                    },
                    TheoryLit {
                        atom: 1,
                        value: true,
                    },
                ]));
            }
            self.accepted = Some(self.trail.assigned.clone());
            FinalCheckOutcome::Sat
        }
    }

    fn lit(var: usize, positive: bool) -> Lit {
        Lit { var, positive }
    }

    /// The complete check rejects a total assignment every partial check
    /// accepted, and the search recovers from it (first half) or refutes on it
    /// (second half).
    ///
    /// **This is the test the `final_check` call site is mutation-checked
    /// against.** Delete `CdclT::run_final_check`'s call to
    /// `TheorySolver::final_check` (or restore the bare `return Outcome::Sat`)
    /// and the driver hands back the very assignment the theory refuses.
    #[test]
    fn final_check_rejects_a_total_assignment_the_asserts_accepted() {
        // (x0 ∨ x1), theory truth "not both true": the Boolean search reaches
        // {x0, x1} first (phase saving is true-first) and only the complete
        // check can see the problem.
        let clauses = vec![vec![lit(0, true), lit(1, true)]];
        let mut solver = CdclT::new(2, 2, clauses, None);
        let mut theory = FinalCheckOnly::new(2, false);
        assert_eq!(solver.solve(&mut theory), Outcome::Sat);
        assert!(
            theory.final_checks >= 2,
            "the first total assignment must have been refused and a second one reached, \
             got {} final checks",
            theory.final_checks
        );
        let accepted = theory
            .accepted
            .as_ref()
            .expect("a Sat verdict comes from an accepted final check");
        assert!(
            !(accepted[0] == Some(true) && accepted[1] == Some(true)),
            "the search returned Sat on an assignment the theory refutes: {accepted:?}"
        );

        // A theory that refutes every total assignment turns a Boolean-SAT
        // skeleton into Unsat.
        let mut solver = CdclT::new(1, 1, vec![vec![lit(0, true)]], None);
        let mut theory = FinalCheckOnly::new(1, true);
        assert_eq!(solver.solve(&mut theory), Outcome::Unsat);
        assert_eq!(theory.final_checks, 1);
    }

    // -----------------------------------------------------------------------
    // (b) the driver-owned propagation queue
    // -----------------------------------------------------------------------

    /// Propagates through the driver-owned queue and **fails the test** if the
    /// driver ever hands it a queue it did not drain, or drains one twice.
    struct QueueTheory {
        trail: Trail,
        /// Set if `propagate_into` was ever entered with a non-empty queue.
        saw_dirty_queue: bool,
        /// Total `(atom, value)` pairs pushed across every call.
        pushed: usize,
        calls: usize,
    }

    impl QueueTheory {
        fn new(atoms: usize) -> Self {
            Self {
                trail: Trail::new(atoms),
                saw_dirty_queue: false,
                pushed: 0,
                calls: 0,
            }
        }
    }

    impl TheorySolver for QueueTheory {
        fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
            self.trail.set(atom, value);
            Ok(())
        }
        fn push(&mut self) {
            self.trail.push();
        }
        fn pop(&mut self) {
            self.trail.pop();
        }
        fn propagate(&self) -> Vec<TheoryProp> {
            unreachable!("propagate_into is overridden; the default must not be reached")
        }
        fn propagate_into(&mut self, queue: &mut PropagationQueue) {
            self.calls += 1;
            if !queue.is_empty() {
                self.saw_dirty_queue = true;
            }
            // atom 0 true entails atom 1 true; atom 1 true entails atom 2 true.
            if self.trail.value(0) == Some(true) && self.trail.value(1).is_none() {
                queue.push_eager(
                    TheoryLit {
                        atom: 1,
                        value: true,
                    },
                    vec![TheoryLit {
                        atom: 0,
                        value: true,
                    }],
                );
                self.pushed += 1;
            }
            if self.trail.value(1) == Some(true) && self.trail.value(2).is_none() {
                queue.push_eager(
                    TheoryLit {
                        atom: 2,
                        value: true,
                    },
                    vec![TheoryLit {
                        atom: 1,
                        value: true,
                    }],
                );
                self.pushed += 1;
            }
        }
    }

    /// The queue arrives empty on every call, and every queued propagation is
    /// applied exactly once.
    #[test]
    fn propagation_queue_arrives_empty_and_is_drained_exactly_once() {
        let mut solver = CdclT::new(3, 3, vec![vec![lit(0, true)]], None);
        let mut theory = QueueTheory::new(3);
        assert_eq!(solver.solve(&mut theory), Outcome::Sat);
        assert!(
            !theory.saw_dirty_queue,
            "the driver handed the theory a queue it had not drained"
        );
        assert!(theory.calls > 0, "propagate_into was never called");
        assert_eq!(
            theory.pushed, 2,
            "each entailed literal is offered once, and is assigned before the next call"
        );
        assert_eq!(
            solver.theory_propagations(),
            2,
            "both queued propagations must reach the trail exactly once"
        );
        assert_eq!(solver.value(1), Some(true));
        assert_eq!(solver.value(2), Some(true));
    }

    // -----------------------------------------------------------------------
    // (c) lazy explanation
    // -----------------------------------------------------------------------

    /// Propagates with **deferred** handles and counts how often the driver
    /// actually asked for a reason. `broken` makes it refuse to resolve a
    /// handle it emitted — the theory-bug case the driver must survive.
    struct LazyTheory {
        trail: Trail,
        /// Atoms entailed true once atom 0 is true.
        entailed: Vec<usize>,
        handles: Vec<(u64, usize)>,
        next_handle: u64,
        lazy_pushes: usize,
        explains: usize,
        broken: bool,
        eager: bool,
    }

    impl LazyTheory {
        fn new(atoms: usize, entailed: Vec<usize>, broken: bool, eager: bool) -> Self {
            Self {
                trail: Trail::new(atoms),
                entailed,
                handles: Vec::new(),
                next_handle: 1,
                lazy_pushes: 0,
                explains: 0,
                broken,
                eager,
            }
        }
    }

    impl TheorySolver for LazyTheory {
        fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
            self.trail.set(atom, value);
            Ok(())
        }
        fn push(&mut self) {
            self.trail.push();
        }
        fn pop(&mut self) {
            self.trail.pop();
        }
        fn propagate(&self) -> Vec<TheoryProp> {
            unreachable!("propagate_into is overridden")
        }
        fn propagate_into(&mut self, queue: &mut PropagationQueue) {
            if self.trail.value(0) != Some(true) {
                return;
            }
            for index in 0..self.entailed.len() {
                let atom = self.entailed[index];
                // Deliberately NOT skipped when the search has already set the
                // atom false: that collision is what forces the driver to ask
                // for the reason, and is the only literal it asks about.
                if self.trail.value(atom) == Some(true) {
                    continue;
                }
                let lit = TheoryLit { atom, value: true };
                if self.eager {
                    queue.push_eager(
                        lit,
                        vec![TheoryLit {
                            atom: 0,
                            value: true,
                        }],
                    );
                } else {
                    let handle = self.next_handle;
                    self.next_handle += 1;
                    self.handles.push((handle, atom));
                    queue.push_lazy(lit, ExplanationId(handle));
                    self.lazy_pushes += 1;
                }
            }
        }
        fn explain(&mut self, handle: ExplanationId) -> Option<Vec<TheoryLit>> {
            self.explains += 1;
            if self.broken {
                return None;
            }
            self.handles
                .iter()
                .find(|(id, _)| *id == handle.0)
                .map(|_| {
                    vec![TheoryLit {
                        atom: 0,
                        value: true,
                    }]
                })
        }
    }

    /// The driver resolves a deferred handle only for the literal it actually
    /// needs a reason for, and leaves the rest unexplained.
    #[test]
    fn lazy_explanation_is_resolved_only_when_the_driver_needs_the_reason() {
        // `[¬x3]` fixes atom 3 false at level 0, so the theory's propagation of
        // atom 3 true collides and needs its reason. Atoms 1, 2 and 4 are
        // propagated and never asked about.
        let clauses = vec![vec![lit(3, false)], vec![lit(0, true), lit(5, true)]];
        let mut solver = CdclT::new(6, 6, clauses, None);
        let mut theory = LazyTheory::new(6, vec![1, 2, 3, 4], false, false);
        let outcome = solver.solve(&mut theory);
        assert_eq!(outcome, Outcome::Sat);
        assert!(
            theory.lazy_pushes >= 3,
            "expected several deferred propagations, got {}",
            theory.lazy_pushes
        );
        assert_eq!(
            theory.explains, 1,
            "exactly the one colliding literal needed its reason; {} deferred pushes were made",
            theory.lazy_pushes
        );
    }

    /// A deferred explanation and the same explanation materialised eagerly
    /// give the same verdict — including on the path where 1-UIP analysis is
    /// what forces the resolution.
    #[test]
    fn lazy_and_eager_explanations_agree_on_the_verdict() {
        for clauses in [
            vec![
                vec![lit(1, false), lit(2, false)],
                vec![lit(0, true), lit(5, true)],
            ],
            vec![vec![lit(3, false)], vec![lit(0, true), lit(5, true)]],
        ] {
            let mut lazy_solver = CdclT::new(6, 6, clauses.clone(), None);
            let mut lazy = LazyTheory::new(6, vec![1, 2, 3, 4], false, false);
            let lazy_outcome = lazy_solver.solve(&mut lazy);

            let mut eager_solver = CdclT::new(6, 6, clauses.clone(), None);
            let mut eager = LazyTheory::new(6, vec![1, 2, 3, 4], false, true);
            let eager_outcome = eager_solver.solve(&mut eager);

            assert_eq!(
                lazy_outcome, eager_outcome,
                "deferred and materialised explanations disagreed on {clauses:?}"
            );
            assert_eq!(eager.explains, 0, "the eager arm must never be asked");
        }
    }

    /// A theory that cannot resolve a handle it emitted is a theory bug. The
    /// driver must degrade to `Unknown` — never to a verdict, and never treat
    /// the missing reason as an empty clause (which would be a wrong `unsat`).
    #[test]
    fn an_unresolvable_lazy_handle_degrades_to_unknown_not_to_a_verdict() {
        // `x0` is a *decision*, not a level-0 unit, so the Boolean conflict on
        // `(¬x1 ∨ ¬x2)` sits above level 0 and 1-UIP analysis must resolve a
        // deferred reason to proceed.
        let clauses = vec![
            vec![lit(1, false), lit(2, false)],
            vec![lit(0, true), lit(5, true)],
        ];
        let mut solver = CdclT::new(6, 6, clauses, None);
        let mut theory = LazyTheory::new(6, vec![1, 2, 3, 4], true, false);
        assert_eq!(solver.solve(&mut theory), Outcome::Unknown);
        assert!(theory.explains > 0, "the driver never asked for the reason");
    }

    // -----------------------------------------------------------------------
    // (d) dynamic atom registration
    // -----------------------------------------------------------------------

    /// Registers a second atom once the first is asserted true, then conflicts
    /// on the pair — so the atom it grew has to be a first-class search
    /// variable, not a dormant one.
    struct GrowingTheory {
        trail: Trail,
        registered: usize,
        pending: usize,
        conflicts: usize,
        asserts: Vec<(usize, bool)>,
    }

    impl GrowingTheory {
        fn new() -> Self {
            Self {
                trail: Trail::new(1),
                registered: 1,
                pending: 0,
                conflicts: 0,
                asserts: Vec::new(),
            }
        }
    }

    impl TheorySolver for GrowingTheory {
        fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
            self.asserts.push((atom, value));
            self.trail.set(atom, value);
            if atom == 0 && value && self.registered == 1 {
                self.registered = 2;
                self.pending = 1;
            }
            // Truth: atom 0 and atom 1 cannot both be true.
            if self.trail.value(0) == Some(true) && self.trail.value(1) == Some(true) {
                self.conflicts += 1;
                return Err(vec![
                    TheoryLit {
                        atom: 0,
                        value: true,
                    },
                    TheoryLit {
                        atom: 1,
                        value: true,
                    },
                ]);
            }
            Ok(())
        }
        fn push(&mut self) {
            self.trail.push();
        }
        fn pop(&mut self) {
            self.trail.pop();
        }
        fn propagate(&self) -> Vec<TheoryProp> {
            Vec::new()
        }
        fn take_new_atoms(&mut self) -> usize {
            std::mem::take(&mut self.pending)
        }
    }

    /// An atom registered mid-search becomes a search variable and its conflict
    /// is learned like any other.
    #[test]
    fn an_atom_registered_mid_search_participates_in_a_conflict() {
        let mut solver = CdclT::new(1, 1, vec![vec![lit(0, true)]], None);
        let mut theory = GrowingTheory::new();
        assert_eq!(solver.solve(&mut theory), Outcome::Sat);
        assert_eq!(
            solver.variable_count(),
            2,
            "the driver must have appended a SAT variable for the registered atom"
        );
        assert_eq!(
            theory.conflicts, 1,
            "the registered atom must have been decided true once and refuted"
        );
        assert!(
            theory.asserts.contains(&(1, true)) && theory.asserts.contains(&(1, false)),
            "the registered atom must have been searched over both polarities, got {:?}",
            theory.asserts
        );
        assert_eq!(solver.value(1), Some(false));
    }
}
