//! Driving the **native** CDCL(T) core from a [`TheorySolver`] (plan slice
//! S7b step 2).
//!
//! S7a taught `axeyum_cnf`'s proof-producing core to decide under a theory and
//! to hand back the ADR-1704 two-stream artifact. Nothing reached it: every
//! shipping route builds `crate::cdclt::CdclT`, which is a second CDCL(T)
//! driver with the same watch scheme, the same order heap and the same clause
//! minimizer (S1, S1b ported all three verbatim) and **no proof output at all**.
//! A refutation from it arrives at the front door as `Evidence::Unsat(None)`
//! with no trusted step: the theory reasoning is trusted and uncounted.
//!
//! This module is the bridge. It is deliberately only the *one-shot* half of
//! the protocol, because that is all but one route needs:
//!
//! | route | protocol |
//! |---|---|
//! | `dl_online`, `lra_theory`, `lia_theory`, `euf_egraph`, `string_theory`, `uflra_online`, `uflia_online` | `CdclT::new` then **one** `solve` |
//! | `ufbv_online` | `with_inactive_variables`, `add_theory_variable`, `add_permanent_clause`, resumed `solve` |
//!
//! So the incremental refinement protocol — dormant variables, permanent
//! clauses, a resumed search retaining the learned database — has exactly one
//! client, and porting it is a separate slice. Everything else can move now.
//!
//! # The two literal conventions, negated once here
//!
//! [`TheorySolver`] carries **asserted literals**: an `assert` conflict is the
//! refuted conjunction (`¬⋀lits` is the lemma), and a propagation reason is the
//! antecedents that force the implied literal.
//! [`axeyum_cnf::theory::NativeTheory`] carries **clauses**: every literal is
//! false under the current assignment, and a propagation reason additionally
//! contains the implied literal itself.
//!
//! [`NativeTheoryAdapter`] is the single place that translation happens, and it
//! happens once per literal. Nothing downstream of it sees the asserted form
//! and nothing upstream of it sees the clause form.

use std::cell::RefCell;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Instant;

use axeyum_cnf::theory::{
    ExplanationId as NativeExplanationId, FinalCheckOutcome as NativeFinalCheck, NativeTheory,
    PropagationQueue as NativeQueue, TheoryExplanation as NativeExplanation,
};
use axeyum_cnf::{
    CnfAssignment, CnfClause, CnfFormula, CnfLit, CnfVar, NativeLayerStatsMirror, TheoryRefutation,
    TheorySolveOptions, TheorySolveOutcome, solve_with_theory_and_drat_proof_mirrored,
};

use crate::cdclt::Lit;
use crate::euf_egraph::{
    ExplanationId, FinalCheckOutcome, PropagationQueue, TheoryEngineCounters, TheoryExplanation,
    TheoryLit, TheorySolver,
};
use crate::layers::TheoryLayerStats;
use crate::live_instruments::{LiveInstruments, LiveSample, Sampled, instrument, publish_live};

thread_local! {
    /// The ADR-1704 artifact of the most recent native CDCL(T) refutation on
    /// this thread, for a caller that reaches the verdict through an API with
    /// nowhere to put it.
    ///
    /// `CheckResult::Unsat` is a unit variant and every route in this crate
    /// returns one, so a refutation's artifact has no channel to the evidence
    /// layer. Rather than widen `CheckResult` (which every backend, every
    /// dispatcher arm and every test would have to move with it), the artifact
    /// is published here and taken there — the same shape
    /// `cdclt_diagnostics::last_theory_layer_stats` already uses for the same
    /// reason.
    ///
    /// **Taken, not read.** [`take_last_theory_refutation`] clears the slot, so
    /// a later `unsat` from a route that produces no artifact cannot pick up
    /// the previous route's, which would attach a trust step to a refutation
    /// that did not produce it.
    static LAST_THEORY_REFUTATION: RefCell<Option<TheoryRefutation>> =
        const { RefCell::new(None) };
}

thread_local! {
    /// How many native CDCL(T) refutations have happened on this thread since
    /// the last [`reset_theory_refutation_channel`].
    ///
    /// **The channel publishes the LAST refutation, so more than one makes it
    /// ambiguous.** A route calls `solve_native` once and returns its verdict,
    /// but `crate::auto` does not: `check_auto` enumerates case-split branches
    /// (`auto.rs:1298`, `auto.rs:1458`) and reports `unsat` only when EVERY
    /// branch was refuted, discarding each branch's `CheckResult::Unsat` on the
    /// way. The artifact left in the slot then refutes the last branch, not the
    /// query, and attaching it to the query's `unsat` would be a fabricated
    /// claim -- the exact shape this repository's evidence discipline exists to
    /// prevent.
    ///
    /// So the counter is not a statistic. It is the guard:
    /// [`take_last_theory_refutation`] hands back an artifact only when exactly
    /// one refutation happened, and declines otherwise. Under-reporting (no
    /// trust step) is safe; over-reporting is not.
    static THEORY_REFUTATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Removes and returns the artifact of the last native CDCL(T) refutation on
/// this thread, leaving the slot empty.
///
/// Returns `None` -- even with an artifact present -- when more than one
/// refutation has happened since the channel was reset, because the slot then
/// names the last of several sub-solves and not the caller's query. See
/// [`THEORY_REFUTATIONS`].
pub(crate) fn take_last_theory_refutation() -> Option<TheoryRefutation> {
    let artifact = LAST_THEORY_REFUTATION.with(|slot| slot.borrow_mut().take());
    if THEORY_REFUTATIONS.with(std::cell::Cell::get) == 1 {
        artifact
    } else {
        None
    }
}

/// Clears the slot without reading it. A route that is about to solve calls
/// this so a verdict it does not reach cannot inherit an older artifact.
pub(crate) fn clear_last_theory_refutation() {
    LAST_THEORY_REFUTATION.with(|slot| *slot.borrow_mut() = None);
}

/// Clears the slot **and** the refutation counter, so the next
/// [`take_last_theory_refutation`] speaks about this solve alone.
///
/// A route clears only the slot ([`clear_last_theory_refutation`], which
/// `solve_native` calls on entry). A caller that spans a whole DISPATCH -- the
/// evidence layer around `crate::auto::solve` -- resets the counter too, which
/// is what makes "exactly one refutation" mean "exactly one inside this
/// dispatch".
pub(crate) fn reset_theory_refutation_channel() {
    clear_last_theory_refutation();
    THEORY_REFUTATIONS.with(|count| count.set(0));
}

thread_local! {
    /// Whether a native CDCL(T) solve on this thread should record its DRAT
    /// stream, i.e. whether an `unsat` should come with the ADR-1704 artifact.
    ///
    /// **Off by default, and that is a measured decision, not caution.** The
    /// stream is every learned clause of the whole search held in memory; on a
    /// long CDCL(T) search that is gigabytes, and `CdclT` -- which emits no
    /// proof at all -- never paid it. Recording unconditionally took the
    /// solver's own unit sweep from 209 s to over 1,800 s. The dispatcher wants
    /// a verdict and pays nothing; the evidence layer, the only consumer of the
    /// artifact, asks for it through [`with_artifact_recording`].
    static RECORD_ARTIFACTS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// How many DRAT literals a route may hold before the recording is abandoned
/// and the refutation reports no artifact.
///
/// Eight million literals is on the order of 64 MB of `CnfLit` plus the `Vec`
/// per step -- enough for every refutation the committed corpora produce
/// through this route, and small enough that a runaway search gives up
/// recording instead of the machine giving up. It bounds the RECORDING only:
/// the search is unaffected either way, so no verdict depends on it.
const PROOF_LITERAL_BUDGET: usize = 8_000_000;

/// Whether the current call should record a proof.
fn recording_artifacts() -> bool {
    RECORD_ARTIFACTS.with(std::cell::Cell::get)
}

/// Runs `f` with artifact recording on, restoring the previous setting after —
/// including on an unwind, since the guard is dropped either way.
pub(crate) fn with_artifact_recording<R>(f: impl FnOnce() -> R) -> R {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            RECORD_ARTIFACTS.with(|flag| flag.set(self.0));
        }
    }
    let _restore = Restore(RECORD_ARTIFACTS.with(|flag| flag.replace(true)));
    f()
}

/// What a native CDCL(T) solve produced.
#[derive(Debug, Clone)]
pub(crate) enum NativeSolveOutcome {
    /// A Boolean- and theory-consistent total assignment. The theory is left in
    /// that state, exactly as `CdclT::solve` leaves it, so the caller builds its
    /// model from the theory plus [`NativeModel`] for the Boolean leaves.
    Sat(NativeModel),
    /// Unsatisfiable modulo the enumerated theory lemmas.
    ///
    /// The artifact itself is **not** a payload here. It travels through
    /// [`take_last_theory_refutation`], because that is the channel the
    /// evidence layer can reach: a route returns a `CheckResult`, whose `Unsat`
    /// is a unit variant, so a payload on this enum would have to be dropped by
    /// every caller anyway. One channel, not two.
    Unsat,
    /// Undecided: the deadline passed, the theory step budget was exhausted, or
    /// the theory could not substantiate an answer. Never a verdict.
    Unknown,
}

/// The Boolean assignment behind a native `sat`, in the shape the routes'
/// model-assembly code already expects (`CdclT::value`).
#[derive(Debug, Clone)]
pub(crate) struct NativeModel {
    assignment: CnfAssignment,
    /// Variables that occur in no clause and were therefore never decided.
    /// `CdclT::value` reports `None` for these; the native core defaults them
    /// `false` in a total assignment. Reporting `None` keeps the routes'
    /// model-injection behaviour identical rather than adding bindings for
    /// symbols the skeleton never constrained.
    occurring: Vec<bool>,
}

impl NativeModel {
    /// The value of `var`, or `None` when the search never assigned it — the
    /// same contract as `CdclT::value`.
    ///
    /// A variable beyond the initial count was appended for a dynamically
    /// registered atom, and the core marks every one of those branchable, so it
    /// is assigned in any total assignment: the `occurring` filter applies only
    /// to the variables the formula was built with.
    pub(crate) fn value(&self, var: usize) -> Option<bool> {
        if var < self.occurring.len() && !self.occurring[var] {
            return None;
        }
        self.assignment.values().get(var).copied()
    }
}

/// Wraps a [`TheorySolver`] so the native CDCL core can drive it.
///
/// Owns the atom↔variable map the native core does not keep: there, atoms *are*
/// variable indices; here atom `a` is variable `var_for_atom[a]`, seeded as the
/// identity over the first `theory_atom_count` variables (exactly what
/// `CdclT::new` builds) and extended on each dynamic registration.
struct NativeTheoryAdapter<'a, T: TheorySolver> {
    theory: &'a mut T,
    /// Where this adapter copies `TheorySolver::engine_counters` while the
    /// search runs, so a watchdog on another thread reads real simplex numbers
    /// instead of `na`.
    ///
    /// The native core cannot do this itself: at its own flush point the theory
    /// is mutably borrowed by the search, so the driver-side counters
    /// (`axeyum_cnf::NativeLayerStatsMirror`) are all it can reach. The adapter
    /// is the one place that holds both. `None` on every solve that did not ask
    /// for a mirror, which is all of them but a `--trace` run under a watchdog.
    engine_mirror: Option<Arc<EngineCountersMirror>>,
    /// `push` calls since the last engine-counter mirror; see
    /// [`ENGINE_MIRROR_PUSHES`].
    engine_pushes: usize,
    /// The atom a SAT variable stands for, `None` for a pure Tseitin variable.
    atom_for_var: Vec<Option<usize>>,
    /// The SAT variable an atom stands for.
    var_for_atom: Vec<usize>,
    /// The index the native core will give the next variable it appends for a
    /// registered atom. The core appends at `assign.len()` and grows by one per
    /// atom, so mirroring that counter keeps the map aligned with no callback.
    next_var: usize,
    /// The solver-side queue, kept for its allocation across rounds exactly as
    /// the native core keeps its own.
    queue: PropagationQueue,
}

impl<'a, T: TheorySolver> NativeTheoryAdapter<'a, T> {
    fn new(
        theory: &'a mut T,
        var_count: usize,
        theory_atom_count: usize,
        engine_mirror: Option<Arc<EngineCountersMirror>>,
    ) -> Self {
        assert!(
            theory_atom_count <= var_count,
            "every theory atom needs a SAT variable"
        );
        let mut atom_for_var = vec![None; var_count];
        for (atom, slot) in atom_for_var.iter_mut().take(theory_atom_count).enumerate() {
            *slot = Some(atom);
        }
        // A theory either keeps a feasibility engine or does not — `TheorySolver`
        // has a default `engine_counters` returning `None`, and an implementor
        // that overrides it returns a struct on every call. Deciding once here
        // means a theory with no engine (`lia_theory`, `euf_egraph`, the string
        // theory) never takes the mirror's lock at all, instead of locking on
        // every complete check to store the same `None`. Measured on a
        // `QF_LIA` pigeonhole through `--trace`: this is the difference between
        // roughly 1% and nothing.
        let engine_mirror = engine_mirror.filter(|_| theory.engine_counters().is_some());
        Self {
            theory,
            engine_mirror,
            engine_pushes: 0,
            atom_for_var,
            var_for_atom: (0..theory_atom_count).collect(),
            next_var: var_count,
            queue: PropagationQueue::new(),
        }
    }

    /// Copies the theory's engine counters to the mirror, if one is installed.
    fn mirror_engine_counters(&self) {
        if let Some(mirror) = self.engine_mirror.as_ref() {
            mirror.store(self.theory.engine_counters());
        }
    }

    /// A `TheoryLit` as the CNF literal that is TRUE when the atom holds the
    /// value the theory named.
    fn cnf_lit(&self, lit: TheoryLit) -> CnfLit {
        let positive = CnfLit::positive(
            CnfVar::new(self.var_for_atom[lit.atom]).expect("atom variable index in range"),
        );
        if lit.value {
            positive
        } else {
            positive.negated()
        }
    }

    /// The conflict CLAUSE for a refuted conjunction of asserted literals:
    /// `¬⋀core`, so every literal is false under the current assignment. This
    /// is the one negation the two conventions differ by.
    fn conflict_clause(&self, core: &[TheoryLit]) -> Vec<CnfLit> {
        core.iter().map(|&l| self.cnf_lit(l).negated()).collect()
    }

    /// The reason CLAUSE for `antecedents ⊨ implied`: `¬⋀antecedents ∨ implied`.
    /// Unit once every antecedent is asserted, which is the invariant 1-UIP
    /// analysis relies on.
    fn reason_clause(&self, antecedents: &[TheoryLit], implied: CnfLit) -> Vec<CnfLit> {
        let mut clause = self.conflict_clause(antecedents);
        clause.push(implied);
        clause
    }
}

impl<T: TheorySolver> NativeTheory for NativeTheoryAdapter<'_, T> {
    fn assert(&mut self, var: usize, value: bool) -> Result<(), Vec<CnfLit>> {
        // A pure Tseitin variable is not an atom and the theory is never told
        // about it — the same test `CdclT::assign` makes.
        let Some(atom) = self.atom_for_var.get(var).copied().flatten() else {
            return Ok(());
        };
        self.theory
            .assert(atom, value)
            .map_err(|core| self.conflict_clause(&core))
    }

    fn push(&mut self) {
        self.theory.push();
        // One decision per `push`, so this is already far coarser than
        // `assert`; the cadence makes it coarser still. With no mirror
        // installed the whole block is one `Option` test on a field the call
        // just touched.
        if self.engine_mirror.is_some() {
            self.engine_pushes += 1;
            if self.engine_pushes.is_multiple_of(ENGINE_MIRROR_PUSHES) {
                self.mirror_engine_counters();
            }
        }
    }

    fn pop(&mut self) {
        self.theory.pop();
    }

    fn propagate_into(&mut self, queue: &mut NativeQueue) {
        // Taken out so the translation loop can borrow `self` immutably while
        // the theory has already finished writing; the allocation goes back.
        let mut solver_queue = core::mem::take(&mut self.queue);
        solver_queue.clear();
        self.theory.propagate_into(&mut solver_queue);
        for (lit, explanation) in solver_queue.entries() {
            // An atom the driver has no variable for is skipped, not indexed:
            // `CdclT::theory_propagate` does exactly this
            // (`let Some(var) = self.theory_variable(lit.atom) else { continue }`),
            // and a theory that offers one is offering a propagation the driver
            // cannot act on rather than committing a contract violation.
            if lit.atom >= self.var_for_atom.len() {
                continue;
            }
            let implied = self.cnf_lit(*lit);
            match explanation {
                TheoryExplanation::Eager(antecedents) => {
                    queue.push_eager(implied, self.reason_clause(antecedents, implied));
                }
                // The lazy channel survives the translation: nothing is
                // materialised until conflict analysis walks past the literal,
                // and `explain` below is told which literal it is explaining so
                // the asserted form can be turned back into a clause then.
                TheoryExplanation::Lazy(handle) => {
                    queue.push_lazy(implied, NativeExplanationId(handle.0));
                }
            }
        }
        self.queue = solver_queue;
    }

    fn final_check(&mut self) -> NativeFinalCheck {
        // Every complete check, not on a cadence: a search can reach a total
        // assignment rarely, and when it does the engine counters have moved
        // the most.
        self.mirror_engine_counters();
        match self.theory.final_check() {
            FinalCheckOutcome::Sat => NativeFinalCheck::Sat,
            FinalCheckOutcome::Unknown => NativeFinalCheck::Unknown,
            FinalCheckOutcome::Conflict(TheoryExplanation::Eager(core)) => {
                NativeFinalCheck::Conflict(NativeExplanation::Eager(self.conflict_clause(&core)))
            }
            FinalCheckOutcome::Conflict(TheoryExplanation::Lazy(handle)) => {
                NativeFinalCheck::Conflict(NativeExplanation::Lazy(NativeExplanationId(handle.0)))
            }
        }
    }

    fn explain(
        &mut self,
        handle: NativeExplanationId,
        implied: Option<CnfLit>,
    ) -> Option<Vec<CnfLit>> {
        let asserted = self.theory.explain(ExplanationId(handle.0))?;
        Some(match implied {
            // A propagation reason: the implied literal plus one false literal
            // per antecedent.
            Some(lit) => self.reason_clause(&asserted, lit),
            // A conflict core: every literal false, nothing else.
            None => self.conflict_clause(&asserted),
        })
    }

    fn take_new_atoms(&mut self) -> usize {
        let fresh = self.theory.take_new_atoms();
        // The core appends `fresh` variables starting at its current variable
        // count, in order, immediately after this call. Mirroring the counter
        // here keeps the map aligned without the core having to report back —
        // and it must happen BEFORE the core asserts any of them.
        for _ in 0..fresh {
            let var = self.next_var;
            self.next_var += 1;
            debug_assert_eq!(self.atom_for_var.len(), var, "variable indices are dense");
            self.atom_for_var.push(Some(self.var_for_atom.len()));
            self.var_for_atom.push(var);
        }
        fresh
    }
}

/// `NativeTheoryAdapter::push` calls between two engine-counter mirrors.
///
/// One `push` is one decision, so this is already a decision cadence; the
/// multiple keeps a decision-heavy search from paying a lock per decision. It
/// bounds how stale a watchdog's simplex numbers can be and nothing else.
const ENGINE_MIRROR_PUSHES: usize = 256;

/// The theory-side counters a *running* search's adapter copies out, for a
/// reader on another thread.
///
/// Separate from `axeyum_cnf::NativeLayerStatsMirror` because the two halves of
/// [`TheoryLayerStats`] come from two places that cannot see each other while
/// the search runs: the driver owns the stage timings and search counters, the
/// `TheorySolver` owns `simplex_pivots` and friends, and at the driver's flush
/// point the theory is mutably borrowed. [`live_theory_layer_stats`] is where
/// the halves are put back together.
#[derive(Debug, Default)]
pub struct EngineCountersMirror {
    /// The most recent counters, or `None` before the first store and for a
    /// theory that keeps no feasibility engine.
    slot: Mutex<Option<TheoryEngineCounters>>,
}

impl EngineCountersMirror {
    /// Stores `counters`, overwriting the previous store. A poisoned lock is
    /// recovered rather than propagated: telemetry must not turn one panic into
    /// two.
    fn store(&self, counters: Option<TheoryEngineCounters>) {
        let mut slot = self.slot.lock().unwrap_or_else(PoisonError::into_inner);
        *slot = counters;
    }

    /// The most recent counters, readable from any thread at any time.
    #[must_use]
    pub fn sample(&self) -> Option<TheoryEngineCounters> {
        *self.slot.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

/// The best theory-layer reading `board` holds: the completed snapshot when the
/// last CDCL(T) search on the worker returned, otherwise a partial reading
/// mirrored out of the search that is still running.
///
/// # Why this is a function and not two `board.sample` calls
///
/// A query runs many searches. The board therefore carries both a `Complete`
/// snapshot of whichever search last returned and a live handle onto whichever
/// one is running now, and which of the two answers the question "what is this
/// query doing" depends on their order: a mirror installed AFTER the last
/// completed snapshot means a search is in flight, and its partial counters are
/// the ones a reader wants, stale though they are. Reversing that would report
/// a finished search's numbers for a file that is currently stuck somewhere
/// else — the kind of stable, wrong number that is worse than no number.
///
/// The returned [`LiveSample::sampled`] says which case it is, and a consumer
/// must print that: an `InFlight` reading is a lower bound on every counter it
/// carries and is never a rate's denominator.
#[must_use]
pub fn live_theory_layer_stats(board: &LiveInstruments) -> Option<LiveSample<TheoryLayerStats>> {
    let completed = board.sample::<TheoryLayerStats>(instrument::THEORY_LAYER);
    let mirror = board.sample::<Arc<NativeLayerStatsMirror>>(instrument::THEORY_LAYER_MIRROR);
    let in_flight = mirror.and_then(|handle| {
        let (native, _flushes) = handle.value.sample()?;
        let engine = board
            .sample::<Arc<EngineCountersMirror>>(instrument::THEORY_ENGINE_MIRROR)
            .and_then(|m| m.value.sample());
        Some(LiveSample {
            value: theory_layer_stats(&native, engine),
            // Always partial: the mirror is written on an iteration cadence
            // from inside the search loop, never at a verdict.
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

/// Runs the native CDCL(T) core over `clauses` with `theory` attached — the
/// one-shot counterpart of `CdclT::new(..).solve(&mut theory)`.
///
/// `theory_atom_count` has the same meaning as `CdclT::new`'s: atoms `0 ..
/// theory_atom_count` are the first that many SAT variables, and every other
/// variable is a Tseitin variable the theory is never told about.
///
/// The conflict budget is unbounded on purpose. `CdclT` has none either; both
/// are bounded by the deadline and by the native core's `THEORY_STEP_BUDGET`,
/// and introducing a conflict cap here would turn searches `CdclT` decides into
/// `Unknown` for a reason unrelated to the engine swap.
pub(crate) fn solve_native<T: TheorySolver>(
    var_count: usize,
    theory_atom_count: usize,
    clauses: &[Vec<Lit>],
    deadline: Option<Instant>,
    theory: &mut T,
) -> NativeSolveOutcome {
    // `CdclT::solve_inner` tests its deadline at the TOP of the main loop, so an
    // already-exhausted budget returns `Outcome::Unknown` having propagated
    // nothing. The native core checks less eagerly, and the difference is
    // observable: measured on `x > 0 & x < 1` with a zero timeout, the core
    // propagated both units, ran a `final_check` the theory had no budget to
    // answer, and returned `Sat`, which `lia_theory` then turned into
    // `Unknown(Incomplete, "model did not replay")` instead of
    // `Unknown(Timeout)` -- a different Unknown KIND, which
    // `dpll_lia::check_with_arith_dpll` branches on. Restoring the eager check
    // here keeps the engine swap a swap: the whole point is that no verdict and
    // no give-up reason moves.
    if deadline.is_some_and(|at| Instant::now() >= at) {
        return NativeSolveOutcome::Unknown;
    }
    let mut formula = CnfFormula::new(var_count);
    let mut occurring = vec![false; var_count];
    for clause in clauses {
        let lits = clause
            .iter()
            .map(|l| {
                occurring[l.var] = true;
                let positive =
                    CnfLit::positive(CnfVar::new(l.var).expect("clause variable index in range"));
                if l.positive {
                    positive
                } else {
                    positive.negated()
                }
            })
            .collect::<Vec<_>>();
        // The only rejection is an out-of-range variable, which the map above
        // has already made impossible.
        formula
            .add_clause(CnfClause::new(lits))
            .expect("clause literals are in range");
    }
    // Collection is read once here and governs both the returned stats and the
    // mirrors: a mirror without collection would publish measured zeros, which
    // is worse than publishing nothing.
    let collect_layer_stats = crate::cdclt::layer_stats_enabled();
    // Only worth building when something can read them. `installed()` is a
    // thread-local `bool`: on a default run this is false and the two `Arc`s,
    // the two `Mutex`es and every store below do not exist.
    let mirroring = collect_layer_stats && crate::live_instruments::installed();
    let layer_mirror = mirroring.then(|| Arc::new(NativeLayerStatsMirror::new()));
    let engine_mirror = mirroring.then(|| Arc::new(EngineCountersMirror::default()));
    if let (Some(layers), Some(engine)) = (layer_mirror.as_ref(), engine_mirror.as_ref()) {
        // Published as HANDLES, not snapshots: the search writes through them
        // for as long as it runs, so a reader always sees the latest flush
        // without the search having to publish again. The sequence numbers are
        // what `live_theory_layer_stats` orders against the completed snapshot
        // `publish_theory_layer_stats` leaves behind when this call returns.
        publish_live(
            instrument::THEORY_ENGINE_MIRROR,
            Arc::clone(engine),
            Sampled::InFlight,
        );
        publish_live(
            instrument::THEORY_LAYER_MIRROR,
            Arc::clone(layers),
            Sampled::InFlight,
        );
    }
    let mut adapter = NativeTheoryAdapter::new(theory, var_count, theory_atom_count, engine_mirror);
    clear_last_theory_refutation();
    // `CdclT`'s heuristics, not the one-shot SAT path's, so moving a route onto
    // this core is a swap of ENGINES and not also a swap of decision
    // heuristics: `CdclT` decides `true` first and does no target rephasing.
    // A model-based consumer can lose a verdict on a different-but-correct
    // model, and one did (see `TheorySolveOptions`).
    // `--trace` is a second consumer behind the same guard `CdclT` reads, and it
    // has to be honoured HERE rather than at construction because on this core
    // collection is a `TheorySolveOptions` field. A route moved onto this engine
    // otherwise stops answering `--trace` silently -- which is what
    // `lra_theory::tests::theory_layer_stats_are_populated_on_a_theory_conflict`
    // caught the moment `lra_theory` moved. Off unless asked: the timing hooks
    // are per-call clock reads.
    let options = TheorySolveOptions {
        initial_phase: true,
        target_rephase: false,
        collect_layer_stats,
        record_proof: recording_artifacts(),
        proof_literal_budget: PROOF_LITERAL_BUDGET,
    };
    let (outcome, native_stats) = solve_with_theory_and_drat_proof_mirrored(
        &formula,
        &mut adapter,
        deadline,
        usize::MAX,
        options,
        layer_mirror,
    );
    if collect_layer_stats {
        // The engine counters come from the THEORY, exactly as
        // `CdclT::theory_layer_stats` takes them, so an LRA route keeps
        // reporting simplex pivots through this engine too.
        crate::cdclt::publish_theory_layer_stats(&theory_layer_stats(
            &native_stats,
            adapter.theory.engine_counters(),
        ));
    }
    match outcome {
        TheorySolveOutcome::Sat(assignment) => NativeSolveOutcome::Sat(NativeModel {
            assignment,
            occurring,
        }),
        TheorySolveOutcome::Unsat(refutation) => {
            // Counted whether or not an artifact was recorded: the guard is
            // about how many refutations HAPPENED, and a recording-off solve
            // that refuted a case-split branch makes the next one ambiguous
            // just the same.
            THEORY_REFUTATIONS.with(|count| count.set(count.get().saturating_add(1)));
            LAST_THEORY_REFUTATION.with(|slot| *slot.borrow_mut() = refutation);
            NativeSolveOutcome::Unsat
        }
        TheorySolveOutcome::ResourceOut | TheorySolveOutcome::Interrupted => {
            NativeSolveOutcome::Unknown
        }
    }
}

/// Lifts the native core's [`axeyum_cnf::NativeLayerStats`] into the
/// [`TheoryLayerStats`] `--trace` already prints, so one channel means the same
/// thing whichever engine ran.
///
/// The fifteen driver-side fields are a field-for-field port (S7b landed them at
/// the same increment sites in the native core); the engine-side fields come
/// from the theory's own `engine_counters`, which is where `CdclT` gets them
/// too. `None` there means "this theory keeps no feasibility engine", never
/// "zero".
fn theory_layer_stats(
    native: &axeyum_cnf::NativeLayerStats,
    engine: Option<crate::euf_egraph::TheoryEngineCounters>,
) -> crate::layers::TheoryLayerStats {
    crate::layers::TheoryLayerStats {
        boolean_propagate: native.boolean_propagate,
        theory_assert: native.theory_assert,
        theory_propagate: native.theory_propagate,
        theory_push_pop: native.theory_push_pop,
        conflict_analysis: native.conflict_analysis,
        theory_final_check: native.theory_final_check,
        theory_explain: native.theory_explain,
        final_checks: native.final_checks,
        theory_conflicts: native.theory_conflicts,
        theory_propagations: native.theory_propagations,
        decisions: native.decisions,
        learned_clauses: native.learned_clauses,
        learned_literals: native.learned_literals,
        learned_literals_before_minimization: native.learned_literals_before_minimization,
        restarts: native.restarts,
        simplex_pivots: engine.map(|e| e.simplex_pivots),
        simplex_checks: engine.map(|e| e.simplex_checks),
        simplex_cold_restarts: engine.map(|e| e.simplex_cold_restarts),
        bound_retractions: engine.map(|e| e.bound_retractions),
        bound_assertions: engine.map(|e| e.bound_assertions),
        theory_propagations_offered: engine.map(|e| e.propagations),
        simplex_rows: engine.map(|e| e.simplex_rows),
        simplex_columns: engine.map(|e| e.simplex_columns),
        // The seven counters below were previously left at `Default` here with a
        // comment saying this constructor "does not measure" them. That was
        // wrong in a way that mattered: they are not driver-side fields at all —
        // every one of them is already carried in the `engine` argument above,
        // filled by `LraTheory::engine_counters`. The constructor was dropping
        // values it held in hand.
        //
        // Why it was expensive: `lra_theory.rs` switched the shipped QF_LRA
        // route from `CdclT` to this native core (ea85c9813, 2026-09-07), so
        // from that commit onward `--trace` printed `final_check_core_widenings=n/a`
        // on *every* QF_LRA file. `n/a` is honest — it says "not measured", not
        // "zero" — but the counter is the pre-registered decision input for
        // whether the Farkas decline paths (`simplex.rs:801-805`, `:823-827`)
        // are the cheap large win, and an absent number reads as a settled one
        // to anybody who measured it on the old route.
        assert_partial_conflicts: engine.map(|e| e.assert_partial_conflicts),
        final_check_conflicts: engine.map(|e| e.final_check_conflicts),
        final_check_core_literals: engine.map(|e| e.final_check_core_literals),
        final_check_core_widenings: engine.map(|e| e.final_check_core_widenings),
        final_check_live_rows: engine.map(|e| e.final_check_live_rows),
        bound_scan_calls: engine.map(|e| e.bound_scan_calls),
        bound_scan_atoms: engine.map(|e| e.bound_scan_atoms),
        pivot_cells_written: engine.map(|e| e.pivot_cells_written),
        pivot_rows_combined: engine.map(|e| e.pivot_rows_combined),
        entering_scan_cells: engine.map(|e| e.entering_scan_cells),
        leaving_scan_rows: engine.map(|e| e.leaving_scan_rows),
        fill_nnz_sum: engine.map(|e| e.fill_nnz_sum),
        fill_samples: engine.map(|e| e.fill_samples),
        bland_fallbacks: engine.map(|e| e.bland_fallbacks),
        farkas_certificates: engine.map(|e| e.farkas_certificates),
        farkas_declined_basic_not_slack: engine.map(|e| e.farkas_declined_basic_not_slack),
        farkas_declined_nonbasic_problem_var: engine
            .map(|e| e.farkas_declined_nonbasic_problem_var),
        farkas_declined_self_check: engine.map(|e| e.farkas_declined_self_check),
    }
}

#[cfg(test)]
mod tests;
