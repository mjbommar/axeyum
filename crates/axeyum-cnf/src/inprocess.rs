//! Proof-carrying inprocessing: run the crate's formula-reducing passes and
//! keep the certificate (ADR-1750).
//!
//! # Why this module exists
//!
//! The [2026-09-07 boolean-core measurement][bench] decomposed
//! `conflicts/s = propagations/s ÷ propagations/conflict` against Kissat 4.0.4
//! over eight `p4dfa` instances on one idle host, and found the deficit is in
//! propagation **volume**, not propagation **speed**: our propagation rate is
//! within ~1.4x, while we need a median **2.56x more propagations per
//! conflict** (up to 7.72x). It pre-registered and refuted the alternatives —
//! restarting 8.4x more often makes the ratio *worse*, and `analyze`'s
//! per-conflict mark array is worth 1.6% — and left exactly one candidate
//! standing, explicitly as *not run* rather than ruled out: Kissat's `probe`
//! umbrella shrinks the formula its propagation runs over, and
//! [`crate::solve_with_drat_proof`] runs none of this crate's own [`crate::vivify`],
//! [`crate::simplify`] or `crate::bve`.
//!
//! [bench]: https://github.com/../docs/research/12-performance/bench-boolean-core-2026-09-07.md
//!
//! # The part that is not a schedule change
//!
//! A solver may reduce its formula however it likes; a solver that also emits a
//! certificate may not do it silently. Every clause a pass adds, strengthens or
//! deletes has to appear in the `DRAT` stream, **in an order in which each added
//! clause is still derivable from what precedes it**, or the proof stops being
//! checkable — and an accepted proof that no longer covers the original formula
//! is worse than a rejected one, because nothing announces it.
//!
//! What this module guarantees, and what its tests assert directly:
//!
//! * The steps this module emits, followed by the search's own steps, form one
//!   `DRAT` proof of the **original** formula — not of the reduced one.
//!   ([`crate::check_drat`] accepts it against the caller's formula.)
//! * Every step any of the three passes emits is plain `RUP`. No `RAT` step, no
//!   extension variable, so nothing here depends on a checker's `RAT` support
//!   or on the pivot-literal convention.
//! * Adds precede the deletions that would remove their justification. That is
//!   the only ordering constraint, and it is enforced at each emission site
//!   rather than by a post-hoc sort.
//! * A `sat` verdict is lifted back through [`Reconstruction`] before it leaves
//!   the core, so the model is over the caller's variables and replays against
//!   the caller's formula.
//!
//! # What each pass costs the certificate
//!
//! | pass | model relation | steps emitted |
//! |---|---|---|
//! | [`crate::simplify`] | model-preserving | `Delete` per subsumed clause; `Add`+`Delete` per strengthening |
//! | [`crate::vivify`] | model-preserving | `Add`+`Delete` per strengthened clause |
//! | `crate::bve` | equisatisfiable | `Add` per resolvent, `Delete` per pivot clause |
//!
//! BVE is the only one that is not model-preserving, and it is also the only one
//! that makes the proof *grow*: it adds resolvents. The others only ever shrink
//! the formula. Note which way round the asymmetry runs — the pass that is
//! weakest on the model side is the one that pays the most for the proof side,
//! and neither fact predicts the other.
//!
//! # Determinism
//!
//! Every pass is deterministic (index-order clause processing, sorted occurrence
//! indices, an explicit work budget), so a fixed formula and fixed
//! [`InprocessOptions`] give a fixed reduced formula and a fixed step sequence.
//! A `deadline`, if one is supplied, is the one input that can change the
//! result — it truncates a pass between clauses, and the partial result is still
//! sound with a still-checkable prefix.

// Monotonic clock for the optional deadline: on wasm32 the browser has no `std`
// clock, so use `web-time`'s drop-in `Instant` (ADR-0017).
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use std::time::Duration;

use crate::bve::{
    BveOptions, BveOutcome, BveStats, Reconstruction, eliminate_variables_within_recorded,
};
use crate::compact::{CompactMap, compact};
use crate::decompose::{
    DecomposeOptions, DecomposeStats, EquivalenceMap, decompose_within_recorded,
};
use crate::simplify::{SubsumeOptions, SubsumeStats, simplify_within_recorded};
use crate::vivify::{VivifyOptions, VivifyStats, vivify_within};
use crate::xor_propagate::{XorPropagation, xor_propagate};
use crate::{CnfFormula, DratSink, DratStep, ProofSinkError, ReductionLink, check_drat};

/// Which reducing passes to run before search, and how hard.
///
/// [`InprocessOptions::OFF`] is the default and is exactly today's behaviour:
/// no pass runs, no step is emitted, the formula reaches the search verbatim.
/// Every entry point that does not name an `InprocessOptions` uses it, so
/// wiring this module in cannot change an existing caller's trajectory,
/// verdict, or `DRAT` stream.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InprocessOptions {
    /// Forward subsumption + self-subsuming resolution ([`crate::simplify`]).
    /// Model-preserving.
    pub subsume: bool,
    /// Clause vivification ([`crate::vivify`]). Model-preserving.
    pub vivify: bool,
    /// Bounded variable elimination (`crate::bve`). Equisatisfiable; a `sat`
    /// model is lifted back through [`InprocessOutcome::reconstruction`].
    pub bve: bool,
    /// Tuning for the subsumption pass (ignored unless [`Self::subsume`]).
    pub subsume_options: SubsumeOptions,
    /// Tuning for the vivification pass (ignored unless [`Self::vivify`]).
    pub vivify_options: VivifyOptions,
    /// Tuning for the elimination pass (ignored unless [`Self::bve`]).
    pub bve_options: BveOptions,
    /// Skip inprocessing entirely above this variable count. The passes are
    /// near-linear with internal budgets, so this is not a hang guard (the
    /// budgets and the optional deadline are); it excludes formulas whose
    /// occurrence lists would not fit a single pass even to start.
    pub max_variables: usize,
    /// Skip inprocessing entirely above this clause count. Same role as
    /// [`Self::max_variables`].
    pub max_clauses: usize,
}

impl InprocessOptions {
    /// No pass runs and no step is emitted — bit-for-bit today's behaviour.
    pub const OFF: Self = Self {
        subsume: false,
        vivify: false,
        bve: false,
        subsume_options: SubsumeOptions::DEFAULT,
        vivify_options: VivifyOptions::DEFAULT,
        bve_options: BveOptions::DEFAULT,
        max_variables: DEFAULT_MAX_VARIABLES,
        max_clauses: DEFAULT_MAX_CLAUSES,
    };

    /// Subsumption then bounded variable elimination — the two passes that
    /// remove clauses and variables, which is what the propagation-volume
    /// hypothesis is about. Vivification is **off** here so that this and
    /// [`Self::preprocess_full`] stay two distinguishable arms for measurement.
    ///
    /// The reason originally given for leaving it off — "it shortens clauses
    /// without removing propagation targets, and it is the most expensive of the
    /// three" — was **measured false on the `QF_BV` parity corpus** on
    /// 2026-09-08 and should not be repeated. Vivification cost 2.7 s across the
    /// 200-file list and bought 8.5 s less BVE, more variables eliminated, and a
    /// better literal ratio; on four files it turned an 11,000 ms BVE into a
    /// 27 ms one by shortening the clauses whose occurrence lists BVE scans.
    ///
    /// **What the shipping SMT path actually does**, because the sentence that
    /// stood here said something a reader would read as the opposite (ADR-1810):
    /// inprocessing is default-**off** (`SolverConfig::cnf_inprocessing` is
    /// `false` at `axeyum-solver/src/backend.rs:390`), and `cnf_vivify` is
    /// default-**on** but is a no-op without it. So "the shipping path enables
    /// vivify by default" is true only in the conditional sense "given
    /// inprocessing, vivify runs". Roadmap 1.2 owns whether that default flips.
    /// See `docs/research/03-measurements/inprocessing-admission-2026-09-08.md`.
    #[must_use]
    pub const fn preprocess() -> Self {
        Self {
            subsume: true,
            vivify: false,
            bve: true,
            ..Self::OFF
        }
    }

    /// All three passes.
    #[must_use]
    pub const fn preprocess_full() -> Self {
        Self {
            vivify: true,
            ..Self::preprocess()
        }
    }

    /// Whether no pass is enabled, in which case [`inprocess_into`] returns the
    /// formula unchanged without touching the sink.
    #[must_use]
    pub const fn is_off(&self) -> bool {
        !self.subsume && !self.vivify && !self.bve
    }
}

impl Default for InprocessOptions {
    fn default() -> Self {
        Self::OFF
    }
}

/// Default admission bound on variables. Chosen above the public-corpus
/// `p4dfa` band so inprocessing is attempted on the instances it can convert;
/// mirrors `axeyum_solver::sat_bv_backend`'s long-standing `INPROCESS_MAX_VARIABLES`.
const DEFAULT_MAX_VARIABLES: usize = 4_000_000;
/// Default admission bound on clauses; mirrors `INPROCESS_MAX_CLAUSES`.
const DEFAULT_MAX_CLAUSES: usize = 16_000_000;

/// What an [`inprocess_into`] run did.
///
/// Every field is a plain count. `clauses_before`/`clauses_after` and
/// `variables_eliminated` are the numbers the propagation-volume hypothesis is
/// stated in; `proof_steps` is what the certificate cost.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct InprocessStats {
    /// Whether any pass actually ran (false when the options are off or the
    /// formula exceeded an admission bound).
    pub ran: bool,
    /// Whether an admission bound rejected the formula.
    pub skipped_size: bool,
    /// Clauses in the caller's formula.
    pub clauses_before: usize,
    /// Clauses in the reduced formula.
    pub clauses_after: usize,
    /// Literal occurrences in the caller's formula.
    pub literals_before: usize,
    /// Literal occurrences in the reduced formula.
    pub literals_after: usize,
    /// `DRAT` steps emitted to the sink by the passes.
    pub proof_steps: usize,
    /// Subsumption pass accounting (zero when it did not run).
    pub subsume: SubsumeStats,
    /// Vivification pass accounting (zero when it did not run).
    pub vivify: VivifyStats,
    /// Elimination pass accounting (zero when it did not run).
    pub bve: BveStats,
}

/// The reduced formula, the model lift, and the accounting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InprocessOutcome {
    /// The reduced formula. Same `variable_count` as the caller's — no pass
    /// renumbers, so a model over this formula is indexed exactly like a model
    /// over the caller's, and the search's `DRAT` steps are literally about the
    /// caller's variables.
    pub formula: CnfFormula,
    /// Lifts a model of [`Self::formula`] to a model of the caller's formula.
    /// Identity unless BVE ran.
    pub reconstruction: Reconstruction,
    /// What each pass did.
    pub stats: InprocessStats,
}

fn literal_count(formula: &CnfFormula) -> usize {
    formula.clauses().iter().map(|c| c.lits().len()).sum()
}

/// Runs the enabled passes on `formula`, emitting their `DRAT` derivation to
/// `sink` in derivation order, and returns the reduced formula plus the model
/// lift.
///
/// The contract that matters: **after this returns `Ok`, a `DRAT` checker fed
/// `formula` and the steps this emitted has an active clause set that entails
/// (in fact contains, up to duplicate copies) every clause of
/// [`InprocessOutcome::formula`]**. So a search over the reduced formula can
/// append its own steps to the same sink and the concatenation is a proof of
/// `formula`.
///
/// The steps go to the sink as they are produced, one pass at a time, so the
/// peak buffer is one pass's derivation rather than the whole prefix. A sink
/// that refuses a step aborts immediately with [`ProofSinkError`]; the caller
/// must then treat the search as undecided, exactly as
/// [`crate::StreamingProofOutcome::SinkFailed`] does — the steps already
/// accepted are a prefix, and a prefix is not a refutation.
///
/// # Errors
///
/// Returns the sink's [`ProofSinkError`] if it refuses a step. Nothing else can
/// fail: the passes are total and their partial results are sound.
pub fn inprocess_into(
    formula: &CnfFormula,
    options: InprocessOptions,
    deadline: Option<Instant>,
    sink: &mut impl DratSink,
) -> Result<InprocessOutcome, ProofSinkError> {
    let mut stats = InprocessStats {
        clauses_before: formula.clauses().len(),
        clauses_after: formula.clauses().len(),
        literals_before: literal_count(formula),
        ..InprocessStats::default()
    };
    stats.literals_after = stats.literals_before;

    if options.is_off() {
        return Ok(InprocessOutcome {
            formula: formula.clone(),
            reconstruction: Reconstruction::default(),
            stats,
        });
    }
    if formula.variable_count() > options.max_variables
        || formula.clauses().len() > options.max_clauses
    {
        stats.skipped_size = true;
        return Ok(InprocessOutcome {
            formula: formula.clone(),
            reconstruction: Reconstruction::default(),
            stats,
        });
    }

    let mut steps: Vec<DratStep> = Vec::new();
    let mut current = formula.clone();
    let mut reconstruction = Reconstruction::default();
    stats.ran = true;

    if options.subsume {
        let (reduced, subsume_stats) = simplify_within_recorded(
            &current,
            options.subsume_options,
            deadline,
            Some(&mut steps),
        );
        stats.subsume = subsume_stats;
        current = reduced;
        stats.proof_steps += flush(&mut steps, sink)?;
    }

    if options.vivify {
        let outcome = vivify_within(&current, options.vivify_options, deadline);
        stats.vivify = outcome.stats;
        current = outcome.formula;
        steps = outcome.proof;
        stats.proof_steps += flush(&mut steps, sink)?;
    }

    if options.bve {
        let outcome = eliminate_variables_within_recorded(
            &current,
            options.bve_options,
            deadline,
            Some(&mut steps),
        );
        stats.bve = outcome.stats;
        current = outcome.formula;
        reconstruction = outcome.reconstruction;
        stats.proof_steps += flush(&mut steps, sink)?;
    }

    stats.clauses_after = current.clauses().len();
    stats.literals_after = literal_count(&current);

    Ok(InprocessOutcome {
        formula: current,
        reconstruction,
        stats,
    })
}

/// Drains `steps` into `sink`, returning how many were emitted.
///
/// Draining rather than iterating is deliberate: the buffer is reused by the
/// next pass, so the peak is one pass's derivation and not the whole prefix.
fn flush(steps: &mut Vec<DratStep>, sink: &mut impl DratSink) -> Result<usize, ProofSinkError> {
    let count = steps.len();
    for step in steps.drain(..) {
        match step {
            DratStep::Add(lits) => sink.add_clause(&lits)?,
            DratStep::Delete(lits) => sink.delete_clause(&lits)?,
        }
    }
    Ok(count)
}

// ---------------------------------------------------------------------------
// The shipping schedule (ADR-1810)
// ---------------------------------------------------------------------------
//
// Everything below is the sequencing `axeyum_solver::sat_bv_backend::inprocess`
// used to carry, moved down here. ADR-1810's reasoning in one line: the two
// pipelines called the same three passes from this crate, the shipping one was
// the superset on every axis that touches a verdict or a certificate, and every
// ingredient it needs -- `xor_propagate`, `compact`, `ReductionLink`, the three
// passes -- was already here, so the move crosses no crate boundary.
//
// What stayed in the solver, and why: the *deadline-derived* work grants (they
// are computed from a solve deadline and host-measured throughput constants, and
// they push their own admission counters) and `SolveStats` itself. Both reach
// this module through [`InprocessObserver`] -- the caller answers "what may this
// pass spend" at the moment the pass is offered, because BVE's grant is computed
// over the *vivified* formula, which does not exist until the schedule is
// half-run.

/// Which occurrence-list pass a work grant is being requested for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OccurrencePass {
    /// Forward subsumption + self-subsuming resolution ([`crate::simplify`]).
    Subsume,
    /// Bounded variable elimination (`crate::bve`).
    Bve,
}

impl OccurrencePass {
    /// The stat-key prefix this pass's counters are named under.
    #[must_use]
    pub const fn stat_prefix(self) -> &'static str {
        match self {
            Self::Subsume => "subsume",
            Self::Bve => "bve",
        }
    }
}

/// The caller's admission policy and telemetry sink for [`inprocess_scheduled`].
///
/// Two methods, because the schedule needs two things from its caller that it
/// cannot decide for itself:
///
/// * [`Self::grant`] — how much work a pass may spend. That is a *policy*
///   decision derived from a solve deadline and host-measured throughput
///   constants, neither of which this crate can see. It is asked at the moment
///   the pass is offered rather than up front, because BVE's grant is computed
///   over the post-subsume, post-vivify formula.
/// * [`Self::count`] — where the per-stage counters go. The keys are named here
///   (they describe this crate's passes); the store they land in belongs to the
///   caller.
///
/// [`NoObserver`] declines every pass and drops every counter, which is the arm
/// a caller uses when it wants the schedule's shape and none of its accounting.
pub trait InprocessObserver {
    /// Work grant for `pass` over `formula`, in occurrence-list steps.
    ///
    /// `None` means the pass **does not run at all**, which is not the same as a
    /// budget of zero: a zero-budget call still builds the occurrence lists, and
    /// that `O(|F|)` setup is exactly the cost a declining caller is declining.
    fn grant(&mut self, pass: OccurrencePass, formula: &CnfFormula) -> Option<u64>;

    /// Records one counter. Called at most once per key per run, in schedule
    /// order.
    fn count(&mut self, name: &str, value: f64);

    /// Work grant for equivalent-literal substitution ([`crate::decompose`])
    /// over `formula`, in graph steps. `None` means the pass does not run.
    ///
    /// **Defaulted to `None` on purpose.** The two occurrence-list passes get a
    /// grant through [`Self::grant`], whose [`OccurrencePass`] is matched
    /// exhaustively by the shipping caller; adding a variant there would make
    /// registering a new pass a change to every implementor, and the change that
    /// compiles is the one that quietly grants the new pass a budget nobody
    /// chose. A defaulted method registers the pass without touching a single
    /// existing observer, and an observer that has not opted in declines it.
    ///
    /// `CaDiCaL`'s own admission rule for this pass —
    /// `effort/1000 x ticks-since-last-run`, refused below `thresh x clauses`,
    /// with `Delay` back-off — is [`crate::DecomposeValve`], which an
    /// implementor of this method can drive directly.
    fn decompose_grant(&mut self, _formula: &CnfFormula) -> Option<u64> {
        None
    }
}

/// An [`InprocessObserver`] that declines every pass and records nothing.
#[derive(Debug, Clone, Copy, Default)]
pub struct NoObserver;

impl InprocessObserver for NoObserver {
    fn grant(&mut self, _pass: OccurrencePass, _formula: &CnfFormula) -> Option<u64> {
        None
    }
    fn count(&mut self, _name: &str, _value: f64) {}
}

/// An [`InprocessObserver`] that grants a fixed budget to every pass and records
/// every counter into a `Vec`, in the order the schedule emitted them.
///
/// Exists so a test can assert on the schedule's *own* telemetry rather than on
/// a re-derivation of it. `grant` is a constant so that "the grant reached the
/// pass" is decidable from `*_work_spent` alone.
#[derive(Debug, Clone, Default)]
pub struct RecordingObserver {
    /// The budget handed to every pass; `None` declines every pass.
    pub budget: Option<u64>,
    /// Every `(name, value)` the schedule recorded, in order.
    pub counts: Vec<(String, f64)>,
}

impl RecordingObserver {
    /// An observer granting `budget` to every pass.
    #[must_use]
    pub fn granting(budget: u64) -> Self {
        Self {
            budget: Some(budget),
            counts: Vec::new(),
        }
    }

    /// The value recorded under `name`, if any.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<f64> {
        self.counts
            .iter()
            .find(|(key, _)| key == name)
            .map(|(_, value)| *value)
    }
}

impl InprocessObserver for RecordingObserver {
    fn grant(&mut self, _pass: OccurrencePass, _formula: &CnfFormula) -> Option<u64> {
        self.budget
    }
    fn count(&mut self, name: &str, value: f64) {
        self.counts.push((name.to_owned(), value));
    }
    fn decompose_grant(&mut self, _formula: &CnfFormula) -> Option<u64> {
        self.budget
    }
}

/// Which stages of the shipping schedule run, and how each is tuned.
///
/// Every field defaults **off** ([`Self::OFF`]). The two occurrence-list passes
/// are turned on by the observer's grant rather than by a flag here — a grant of
/// `None` is the only way to say "do not run this pass", and keeping that in one
/// place is what stops "budget computed, pass run with defaults" from being a
/// one-character edit that compiles.
// A flat set of independent stage switches, every one of which is named at the
// only call site that builds it. The lint targets boolean-blind *positional*
// arguments; folding these into nested option types would hide the one property
// the shipping caller has to be able to read off in one glance -- which stages
// are on -- and ADR-1810 records that reaching for a preset by name is exactly
// how the `vivify` default was nearly changed by accident.
#[allow(clippy::struct_excessive_bools)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InprocessSchedule {
    /// Recover the XOR gates entailed by the formula, Gaussian-solve them and
    /// append the implied units before the passes run.
    ///
    /// Skipped when [`Self::recording`] is set and the pass found any unit: a
    /// Gaussian-implied unit is not `RUP` in general, so it would be the one
    /// link in the chain no `DRAT` step could justify. Dropping it costs
    /// propagation speed, not soundness.
    pub xor_propagate: bool,
    /// Clause count above which [`Self::xor_propagate`] is skipped. Gaussian
    /// elimination over the recovered system is `O(gates²·vars)` and carries no
    /// internal deadline, so it needs a cap of its own.
    pub xor_propagate_max_clauses: usize,
    /// Run equivalent-literal substitution ([`crate::decompose`]) before the
    /// occurrence-list passes.
    ///
    /// It goes first because it is the cheapest pass and the one whose output
    /// every later pass benefits from — a formula with `k` fewer variables is a
    /// smaller occurrence-list problem for both subsumption and BVE. It is also
    /// the pass most helped by running *again* afterwards, since both of those
    /// shorten clauses and a clause shortened to two literals is a new edge;
    /// `DecomposeOptions::max_rounds` covers the rounds this pass creates for
    /// itself, and a second scheduled offer would cover the rest.
    ///
    /// The flag alone does not run it: [`InprocessObserver::decompose_grant`]
    /// must also return a budget, which no existing observer does.
    pub decompose: bool,
    /// Tuning for the substitution pass (ignored unless [`Self::decompose`]).
    pub decompose_options: DecomposeOptions,
    /// Run clause vivification between subsumption and elimination.
    pub vivify: bool,
    /// Tuning for vivification (ignored unless [`Self::vivify`]).
    pub vivify_options: VivifyOptions,
    /// Step-check vivification's own `DRAT` against the pre-vivify formula
    /// before accepting the strengthened clauses, falling back to the
    /// un-vivified formula if any step fails to verify.
    ///
    /// A cheap local alarm that names vivify as the culprit, where a link
    /// failure only says the concatenation did not verify. Model-preserving
    /// either way, so the fallback cannot change a verdict.
    pub vivify_step_guard: bool,
    /// Whether BVE drops lazily-removed clause ids from its occurrence lists.
    pub bve_compact_occurrences: bool,
    /// Record every pass's derivation into [`ScheduledInprocess::link`].
    ///
    /// Off costs nothing and is the right default: a prefix is a
    /// `Vec<DratStep>` proportional to the **formula** (ADR-1750 measured BVE's
    /// at 37.7 M steps on a 3.1 M-variable instance), which is not something to
    /// pay for on a path that will never check it.
    pub recording: bool,
}

impl InprocessSchedule {
    /// No optional stage runs. Compaction still does — see
    /// [`inprocess_scheduled`].
    pub const OFF: Self = Self {
        xor_propagate: false,
        xor_propagate_max_clauses: 0,
        decompose: false,
        decompose_options: DecomposeOptions::DEFAULT,
        vivify: false,
        vivify_options: VivifyOptions::DEFAULT,
        vivify_step_guard: false,
        bve_compact_occurrences: false,
        recording: false,
    };
}

impl Default for InprocessSchedule {
    fn default() -> Self {
        Self::OFF
    }
}

/// What [`inprocess_scheduled`] produced: the formula to search, both model
/// lifts, and the refutation lift.
///
/// Note which direction each map runs. `compaction` and `reconstruction` carry
/// **models** up from the reduced formula to the original; `link` carries a
/// **refutation** the same way. They are not inverses of each other and neither
/// substitutes for the other: BVE is equisatisfiable, so the `sat` direction
/// needs the reconstruction stack and the `unsat` direction needs the
/// resolvents' derivation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScheduledInprocess {
    /// The compacted, reduced formula to hand the search.
    pub formula: CnfFormula,
    /// Lifts a compacted model up to the reduced (original-width) variables.
    pub compaction: CompactMap,
    /// Lifts a reduced model back to the original pre-BVE variables.
    pub reconstruction: Reconstruction,
    /// Fills in the variables equivalent-literal substitution removed. Identity
    /// unless [`InprocessSchedule::decompose`] ran and substituted something.
    ///
    /// **A caller that lifts a model must apply this too.** A substituted
    /// variable does not occur in [`Self::formula`], so its slot in a search's
    /// model is a placeholder, not a value — and a placeholder that happens to
    /// replay is the failure mode this field exists to prevent.
    /// [`Self::lift_model`] applies all three lifts in the one order that is
    /// correct.
    pub equivalences: EquivalenceMap,
    /// Whether substitution found a component holding both polarities of one
    /// variable, which refutes the formula outright.
    ///
    /// [`Self::formula`] is then the **unreduced** formula and [`Self::link`],
    /// under [`InprocessSchedule::recording`], already derives the empty clause.
    /// A caller that ignores this flag searches a formula that is genuinely
    /// unsatisfiable and decides it independently, so ignoring it costs time,
    /// never correctness.
    pub decompose_unsat: bool,
    /// The passes' own `DRAT` derivation plus the compaction's variable
    /// bijection, so a refutation of [`Self::formula`] lifts to a refutation of
    /// the caller's formula. Empty and identity unless
    /// [`InprocessSchedule::recording`] asked for it.
    pub link: ReductionLink,
}

impl ScheduledInprocess {
    /// Lifts a model of [`Self::formula`] all the way back to the caller's
    /// variables, applying every lift in the only order that is correct.
    ///
    /// `compaction.expand` first (the search's model is over compacted
    /// variables), then `reconstruction.extend` (BVE's eliminated variables are
    /// defined by clauses over the *post-substitution* formula, so they need
    /// their neighbours' values, not their neighbours' pre-images), then
    /// `equivalences.extend` (a substituted variable's representative may itself
    /// have been eliminated by BVE, so it must already be filled in).
    ///
    /// Existing callers compose the first two by hand. This method exists so
    /// that adding the third is not something a caller can forget: the order is
    /// stated once, here, rather than at every lift site.
    #[must_use]
    pub fn lift_model(&self, compacted: &[bool]) -> Vec<bool> {
        let reduced = self.compaction.expand(compacted);
        let extended = self.reconstruction.extend(&reduced);
        self.equivalences.extend(&extended)
    }
}

/// Runs the shipping inprocessing schedule — XOR propagation, subsumption,
/// optional vivification, bounded variable elimination, then compaction —
/// recording the whole reduction into a [`ReductionLink`] when asked.
///
/// # The contract that matters
///
/// With [`InprocessSchedule::recording`] set,
/// `link.check_unsat(caller_formula, result.formula, search_proof, cap)` verifies
/// a refutation of [`ScheduledInprocess::formula`] **against the caller's
/// formula**: the link holds every step the passes derived, in derivation order,
/// plus the renumbering `compact` applied, so the search's steps can be lifted
/// out of the compacted variable space and concatenated onto the prefix. Without
/// the renaming half the prefix talks about original variables and the search's
/// steps talk about compacted ones, and no concatenation of the two is a proof
/// of anything — which is why compaction is inside this function rather than
/// beside it.
///
/// A `sat` model of [`ScheduledInprocess::formula`] lifts the other way, through
/// `compaction.expand` and then `reconstruction.extend`, in that order.
///
/// # Compaction is not optional
///
/// It always runs. It is a pure renumbering bijection on the live set so it
/// cannot change `sat`/`unsat`; it is what makes the result's `variable_count`
/// mean what a variable-bound admission gate thinks it means; and making it
/// optional would add an arm no caller uses. A caller that wants a flat `DRAT`
/// stream over unrenumbered variables wants [`inprocess_into`] instead — that is
/// the streaming entry point, and it is unchanged.
///
/// # Stage attribution
///
/// Every stage is timed separately and each records whether `deadline` had
/// already expired when it returned. A single `inprocess_ms` attributes the
/// whole spend to "inprocessing", which is the same mistake as attributing a
/// solve to the last route that ran: the stage that consumed the time and the
/// stage that was running when the clock ran out are different questions, and a
/// scheduling decision needs both.
// The stage clocks stay next to the work they measure. Splitting this would put
// each stage's `Instant` in a different function from the stage it times, which
// is exactly the arrangement that lets a cost hide inside a neighbouring stage.
#[allow(clippy::too_many_lines)]
pub fn inprocess_scheduled(
    formula: &CnfFormula,
    schedule: InprocessSchedule,
    deadline: Option<Instant>,
    observer: &mut impl InprocessObserver,
) -> ScheduledInprocess {
    observer.count(
        "inprocess_literals_before",
        usize_as_f64(literal_count(formula)),
    );

    // --- XOR propagation ---------------------------------------------------
    // Each added unit is entailed by the formula (the recognized gates are
    // equivalent to clause-subsets of it), so it removes no models and adds
    // none — the augmented formula is logically equivalent and needs no extra
    // reconstruction. The contradictory-subsystem (`Unsat`) verdict is NOT
    // trusted as a certificate here (no XOR proof emitter yet); that formula is
    // left unchanged for the checked SAT solve to refute independently.
    let xor_start = Instant::now();
    let xor_base: Option<CnfFormula> = if !schedule.xor_propagate {
        None
    } else if formula.clauses().len() <= schedule.xor_propagate_max_clauses {
        match xor_propagate(formula) {
            XorPropagation::Propagated {
                formula: augmented,
                stats: xstats,
            } => {
                observer.count("xor_gates_recognized", usize_as_f64(xstats.xors_recognized));
                observer.count("xor_units_added", usize_as_f64(xstats.units_added));
                observer.count(
                    "xor_equalities_available",
                    usize_as_f64(xstats.equalities_available),
                );
                if schedule.recording && xstats.units_added > 0 {
                    observer.count("xor_propagate_skipped_for_proof", 1.0);
                    None
                } else {
                    (xstats.units_added > 0).then_some(augmented)
                }
            }
            XorPropagation::Unsat => {
                observer.count("xor_subsystem_unsat", 1.0);
                None
            }
        }
    } else {
        observer.count("xor_propagate_skipped_size", 1.0);
        None
    };
    count_duration_ms(observer, "xor_propagate_ms", xor_start.elapsed());
    let base: &CnfFormula = xor_base.as_ref().unwrap_or(formula);

    let mut link = ReductionLink::identity();
    let recording = schedule.recording;
    let mut steps: Vec<DratStep> = Vec::new();

    // --- Equivalent-literal substitution -----------------------------------
    // Equisatisfiable, not model-preserving: a substituted variable leaves the
    // formula entirely, so its slot in a model is filled by `equivalences`
    // rather than by the search. Every step it emits is plain `RUP` and the
    // derivation order is the pass's own contract (`crate::decompose`), so its
    // prefix joins the link like any other pass's.
    let decompose_start = Instant::now();
    let (substituted, equivalences, decompose_stats) =
        run_decompose(&schedule, base, observer, recording.then_some(&mut steps));
    if schedule.decompose {
        if recording {
            observer.count("decompose_proof_steps", usize_as_f64(steps.len()));
            link.record(steps.drain(..));
        } else {
            steps.clear();
        }
        count_duration_ms(observer, "decompose_ms", decompose_start.elapsed());
        observer.count("decompose_ran", f64::from(u8::from(decompose_stats.ran)));
        observer.count("decompose_rounds", usize_as_f64(decompose_stats.rounds));
        observer.count(
            "decompose_binary_clauses",
            usize_as_f64(decompose_stats.binary_clauses),
        );
        observer.count("decompose_classes", usize_as_f64(decompose_stats.classes));
        observer.count(
            "decompose_variables_substituted",
            usize_as_f64(decompose_stats.variables_substituted),
        );
        observer.count(
            "decompose_clauses_rewritten",
            usize_as_f64(decompose_stats.clauses_rewritten),
        );
        observer.count(
            "decompose_clauses_removed",
            usize_as_f64(decompose_stats.clauses_removed),
        );
        observer.count(
            "decompose_work_spent",
            u64_as_f64(decompose_stats.work_spent),
        );
        observer.count(
            "decompose_work_exhausted",
            f64::from(u8::from(decompose_stats.work_exhausted)),
        );
        observer.count(
            "decompose_unsat",
            f64::from(u8::from(decompose_stats.unsat)),
        );
    }
    let base: &CnfFormula = &substituted;

    // --- Subsumption -------------------------------------------------------
    // The timer starts before the grant is requested: deciding admission reads
    // the formula, and that read is part of what the stage cost.
    let subsume_start = Instant::now();
    let subsume_grant = observer.grant(OccurrencePass::Subsume, base);
    let (simplified, subsume) = run_subsume(
        base,
        subsume_grant,
        deadline,
        recording.then_some(&mut steps),
    );
    if recording {
        observer.count("subsume_proof_steps", usize_as_f64(steps.len()));
        link.record(steps.drain(..));
    }
    count_duration_ms(observer, "subsume_ms", subsume_start.elapsed());
    count_deadline_expired(observer, "subsume_deadline_expired", deadline);
    observer.count("subsume_work_spent", u64_as_f64(subsume.work_spent));
    observer.count(
        "subsume_work_at_last_progress",
        u64_as_f64(subsume.work_at_last_progress),
    );
    observer.count(
        "subsume_dead_occurrence_entries",
        u64_as_f64(subsume.dead_occurrence_entries),
    );
    observer.count(
        "subsume_work_exhausted",
        f64::from(u8::from(subsume.work_exhausted)),
    );

    // --- Vivification ------------------------------------------------------
    // Model-preserving (same satisfying assignments, same `variable_count`, no
    // reconstruction trail), so its output feeds BVE in place of `simplified`
    // and the model-lift stack is unchanged.
    let vivify_start = Instant::now();
    let vivified = maybe_vivify(&schedule, &simplified, deadline, observer, &mut link);
    if schedule.vivify {
        count_duration_ms(observer, "vivify_ms", vivify_start.elapsed());
        count_deadline_expired(observer, "vivify_deadline_expired", deadline);
    }

    // --- Bounded variable elimination --------------------------------------
    let bve_start = Instant::now();
    let bve_grant = observer.grant(OccurrencePass::Bve, &vivified);
    let bve = run_bve(
        &vivified,
        bve_grant,
        deadline,
        schedule.bve_compact_occurrences,
        recording.then_some(&mut steps),
    );
    if recording {
        observer.count("bve_proof_steps", usize_as_f64(steps.len()));
        link.record(steps.drain(..));
    }
    count_duration_ms(observer, "bve_ms", bve_start.elapsed());
    count_deadline_expired(observer, "bve_deadline_expired", deadline);
    observer.count("bve_work_spent", u64_as_f64(bve.stats.work_spent));
    observer.count(
        "bve_work_at_last_elimination",
        u64_as_f64(bve.stats.work_at_last_elimination),
    );
    observer.count(
        "bve_dead_occurrence_entries",
        u64_as_f64(bve.stats.dead_occurrence_entries),
    );
    observer.count(
        "bve_work_exhausted",
        f64::from(u8::from(bve.stats.work_exhausted)),
    );

    observer.count("cnf_inprocessing", 1.0);
    observer.count(
        "subsume_tautologies_removed",
        usize_as_f64(subsume.tautologies_removed),
    );
    observer.count(
        "subsume_clauses_subsumed",
        usize_as_f64(subsume.clauses_subsumed),
    );
    observer.count(
        "subsume_literals_strengthened",
        usize_as_f64(subsume.literals_strengthened),
    );
    observer.count(
        "bve_variables_eliminated",
        usize_as_f64(bve.stats.variables_eliminated),
    );
    observer.count(
        "bve_clauses_removed",
        usize_as_f64(bve.stats.clauses_removed),
    );
    observer.count("bve_clauses_added", usize_as_f64(bve.stats.clauses_added));

    // --- Compaction --------------------------------------------------------
    // BVE removes clauses/variables but never renumbers, so its reduced formula
    // still reports the original (wide) `variable_count`. Densely renumber the
    // live variables so a var-bound admission gate sees the real count.
    let bve_variable_count = bve.formula.variable_count();
    let compact_start = Instant::now();
    let (compacted, compaction) = compact(&bve.formula);
    // Compose the renumbering into the link. THIS is the step whose absence kept
    // the shipping backend checking against the reduced formula: without it the
    // prefix talks about original variables and the search's steps talk about
    // compacted ones.
    if recording {
        let new_to_old: Vec<usize> = (0..compaction.live_count())
            .map(|new| compaction.original_of(new))
            .collect();
        link.rename(&new_to_old);
    }
    count_duration_ms(observer, "compact_ms", compact_start.elapsed());
    let compacted_variable_count = compacted.variable_count();
    observer.count(
        "inprocess_literals_after",
        usize_as_f64(literal_count(&compacted)),
    );
    observer.count(
        "cnf_compaction_variables_before",
        usize_as_f64(bve_variable_count),
    );
    observer.count(
        "cnf_compaction_variables_after",
        usize_as_f64(compacted_variable_count),
    );
    observer.count(
        "cnf_compaction_variables_dropped",
        usize_as_f64(bve_variable_count.saturating_sub(compacted_variable_count)),
    );
    // The clause count is unchanged by compaction (renumbering only), so the
    // submitted clause count is the BVE-reduced count.
    observer.count(
        "cnf_clauses_solved",
        usize_as_f64(compacted.clauses().len()),
    );
    observer.count(
        "cnf_variables_solved",
        usize_as_f64(compacted_variable_count),
    );

    if recording {
        observer.count("inprocess_proof_steps", usize_as_f64(link.prefix_len()));
        observer.count(
            "inprocess_link_checkable",
            f64::from(u8::from(link.is_checkable())),
        );
    }

    ScheduledInprocess {
        formula: compacted,
        compaction,
        reconstruction: bve.reconstruction,
        equivalences,
        decompose_unsat: decompose_stats.unsat,
        link,
    }
}

/// Runs equivalent-literal substitution when the schedule asks for it **and**
/// the observer grants a budget, returning the substituted formula, the model
/// lift, and the accounting.
///
/// A named function rather than a `match` at the call site, for the reason
/// [`run_subsume`] gives and with the same mutation history behind it: with the
/// decision inline, computing a budget and then handing the pass
/// `DecomposeOptions::DEFAULT` compiles, runs, and is caught by nothing.
///
/// `None` from the grant means the pass does not run at all — not a budget of
/// zero. A zero-budget call still scans every clause to size the implication
/// graph, and that `O(|F|)` scan is exactly what a refusal declines to pay.
fn run_decompose(
    schedule: &InprocessSchedule,
    formula: &CnfFormula,
    observer: &mut impl InprocessObserver,
    proof: Option<&mut Vec<DratStep>>,
) -> (CnfFormula, EquivalenceMap, DecomposeStats) {
    if !schedule.decompose {
        return (
            formula.clone(),
            EquivalenceMap::identity(formula.variable_count()),
            DecomposeStats::default(),
        );
    }
    let Some(work_budget) = observer.decompose_grant(formula) else {
        observer.count("decompose_declined", 1.0);
        return (
            formula.clone(),
            EquivalenceMap::identity(formula.variable_count()),
            DecomposeStats::default(),
        );
    };
    let outcome = decompose_within_recorded(
        formula,
        DecomposeOptions {
            work_budget: Some(work_budget),
            ..schedule.decompose_options
        },
        proof,
    );
    (outcome.formula, outcome.equivalences, outcome.stats)
}

/// Runs subsumption under `grant`, or not at all.
///
/// A named function rather than a `match` at the call site so the wiring itself
/// is testable. It is a real gap otherwise: with the decision inline, computing
/// the budget correctly and then handing the pass `SubsumeOptions::DEFAULT`
/// compiles, runs, produces identical answers, and is caught by nothing —
/// verified by mutation, where exactly that edit survived a whole
/// `--lib --features full` sweep.
///
/// `None` means the pass does not run at all, which is **not** the same as
/// running it with a budget of zero: a zero-budget call still normalizes every
/// clause and builds the first round's occurrence lists, and that `O(|F|)` setup
/// is exactly the cost the admission test declined to pay.
fn run_subsume(
    formula: &CnfFormula,
    grant: Option<u64>,
    deadline: Option<Instant>,
    proof: Option<&mut Vec<DratStep>>,
) -> (CnfFormula, SubsumeStats) {
    match grant {
        Some(work_budget) => simplify_within_recorded(
            formula,
            SubsumeOptions {
                work_budget: Some(work_budget),
            },
            deadline,
            proof,
        ),
        None => (formula.clone(), SubsumeStats::default()),
    }
}

/// Runs BVE under `grant`, or not at all. The same wiring gap [`run_subsume`]
/// exists to close, in the same shape and with the same mutation history.
///
/// `None` means the pass does not run at all, which is **not** the same as a
/// budget of zero: a zero-budget call still builds the occurrence lists, and
/// that `O(|F|)` setup is exactly the cost being declined.
fn run_bve(
    formula: &CnfFormula,
    grant: Option<u64>,
    deadline: Option<Instant>,
    compact_occurrences: bool,
    proof: Option<&mut Vec<DratStep>>,
) -> BveOutcome {
    match grant {
        Some(work_budget) => eliminate_variables_within_recorded(
            formula,
            BveOptions {
                work_budget: Some(work_budget),
                compact_occurrences,
                ..BveOptions::DEFAULT
            },
            deadline,
            proof,
        ),
        None => BveOutcome::skipped(formula),
    }
}

/// Runs clause vivification when the schedule asks for it, returning the
/// strengthened (model-preserving) formula; otherwise returns `simplified`
/// unchanged.
///
/// Under [`InprocessSchedule::vivify_step_guard`] the pass's `DRAT` is
/// step-checked as a standalone guard: every step must verify against the
/// pre-vivify formula. [`crate::check_drat`] returns `Ok(true)` only when the
/// proof also derives the empty clause (a strengthening collapsing to `()`) and
/// `Ok(false)` for an ordinary strengthening that verifies but does not refute —
/// both are step-sound; only `Err` (an unjustified add) is a soundness alarm. So
/// the guard is `is_ok()`, matching vivify's own tests. A failed step-check
/// discards the strengthening; the verdict is unaffected either way, since
/// vivify is model-preserving.
fn maybe_vivify(
    schedule: &InprocessSchedule,
    simplified: &CnfFormula,
    deadline: Option<Instant>,
    observer: &mut impl InprocessObserver,
    link: &mut ReductionLink,
) -> CnfFormula {
    if !schedule.vivify {
        return simplified.clone();
    }
    let outcome = vivify_within(simplified, schedule.vivify_options, deadline);
    if schedule.vivify_step_guard {
        let step_ok = check_drat(simplified, &outcome.proof).is_ok();
        observer.count("vivify_drat_step_checked", if step_ok { 1.0 } else { 0.0 });
        if !step_ok {
            // Conservative: discard the (unverifiable) strengthening and proceed
            // on the pre-vivify formula.
            return simplified.clone();
        }
    }
    // The pass's derivation joins the link, so its strengthenings are part of
    // the certificate rather than a step-checked side-guard.
    if schedule.recording {
        observer.count("vivify_proof_steps", usize_as_f64(outcome.proof.len()));
        link.record(outcome.proof.iter().cloned());
    }
    observer.count(
        "vivify_clauses_strengthened",
        usize_as_f64(outcome.stats.clauses_strengthened),
    );
    observer.count(
        "vivify_literals_removed",
        usize_as_f64(outcome.stats.literals_removed),
    );
    observer.count(
        "vivify_clauses_removed",
        usize_as_f64(outcome.stats.clauses_removed),
    );
    outcome.formula
}

fn count_duration_ms(observer: &mut impl InprocessObserver, name: &str, elapsed: Duration) {
    observer.count(name, elapsed.as_secs_f64() * 1000.0);
}

/// Records whether `deadline` had **already expired** when the calling stage
/// returned — the direct discriminator between "the pass is expensive" and "the
/// clock cut the pass off after it paid its setup cost".
///
/// The key is absent when there is no deadline at all, so a missing key means
/// "truncation was impossible here", not "did not happen". It is checked at the
/// stage boundary rather than inside each pass: the passes' internal break sites
/// conflate an expired deadline with an exhausted work budget, and this
/// observable does not.
fn count_deadline_expired(
    observer: &mut impl InprocessObserver,
    name: &str,
    deadline: Option<Instant>,
) {
    if let Some(dl) = deadline {
        observer.count(name, if Instant::now() >= dl { 1.0 } else { 0.0 });
    }
}

#[allow(clippy::cast_precision_loss)]
fn usize_as_f64(value: usize) -> f64 {
    value as f64
}

#[allow(clippy::cast_precision_loss)]
fn u64_as_f64(value: u64) -> f64 {
    value as f64
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CnfClause, CnfFormula, CnfLit, CnfVar, ProofSolveOutcome, SatResult, VecProofSink,
        check_drat, solve_with_drat_proof, solve_with_native_core,
    };

    fn v(i: usize) -> CnfVar {
        CnfVar::new(i).expect("var")
    }
    fn p(i: usize) -> CnfLit {
        CnfLit::positive(v(i))
    }
    fn n(i: usize) -> CnfLit {
        CnfLit::positive(v(i)).negated()
    }
    fn formula(nvars: usize, clauses: &[&[CnfLit]]) -> CnfFormula {
        let mut f = CnfFormula::new(nvars);
        for c in clauses {
            f.add_clause(CnfClause::new(c.to_vec())).expect("in range");
        }
        f
    }

    /// A small unsatisfiable formula with structure all three passes bite on:
    /// duplicate clauses (subsumption), a strengthenable clause (self-subsuming
    /// resolution), and low-occurrence variables (elimination).
    fn pigeonhole_3_2() -> CnfFormula {
        // 3 pigeons, 2 holes. x_{p,h} = var 2p + h.
        let mut f = CnfFormula::new(6);
        for pigeon in 0..3 {
            f.add_clause(CnfClause::new(vec![p(2 * pigeon), p(2 * pigeon + 1)]))
                .expect("in range");
        }
        for hole in 0..2 {
            for a in 0..3 {
                for b in (a + 1)..3 {
                    f.add_clause(CnfClause::new(vec![n(2 * a + hole), n(2 * b + hole)]))
                        .expect("in range");
                }
            }
        }
        f
    }

    fn all_options() -> Vec<(&'static str, InprocessOptions)> {
        vec![
            (
                "subsume",
                InprocessOptions {
                    subsume: true,
                    ..InprocessOptions::OFF
                },
            ),
            (
                "vivify",
                InprocessOptions {
                    vivify: true,
                    ..InprocessOptions::OFF
                },
            ),
            (
                "bve",
                InprocessOptions {
                    bve: true,
                    ..InprocessOptions::OFF
                },
            ),
            ("preprocess", InprocessOptions::preprocess()),
            ("preprocess_full", InprocessOptions::preprocess_full()),
        ]
    }

    #[test]
    fn off_is_the_identity_and_emits_nothing() {
        let f = pigeonhole_3_2();
        let mut sink = VecProofSink::new();
        let out = inprocess_into(&f, InprocessOptions::OFF, None, &mut sink).expect("infallible");
        assert_eq!(out.formula, f);
        assert!(sink.into_steps().is_empty());
        assert!(!out.stats.ran);
    }

    /// The prefix each pass emits is a `DRAT` derivation of the **original**
    /// formula on its own, before any search step is appended.
    #[test]
    fn every_pass_prefix_checks_against_the_original() {
        let f = pigeonhole_3_2();
        for (name, options) in all_options() {
            let mut sink = VecProofSink::new();
            let out = inprocess_into(&f, options, None, &mut sink).expect("infallible");
            let steps = sink.into_steps();
            // `check_drat` returns Ok(false) when the empty clause was not
            // derived, which is the expected shape for a prefix that only
            // reduces. What must never happen is `Err` — a step that does not
            // verify.
            assert!(
                check_drat(&f, &steps).is_ok(),
                "{name}: prefix has a step that does not verify"
            );
            assert_eq!(out.stats.proof_steps, steps.len(), "{name}: step count");
        }
    }

    /// Every pass preserves satisfiability, and a model of the reduced formula
    /// lifts to a model of the original.
    #[test]
    fn reduction_preserves_satisfiability_and_lifts_models() {
        // Satisfiable: 2 pigeons, 2 holes.
        let f = formula(
            4,
            &[
                &[p(0), p(1)],
                &[p(2), p(3)],
                &[n(0), n(2)],
                &[n(1), n(3)],
                // A duplicate and a strengthenable clause, so subsumption bites.
                &[p(0), p(1)],
                &[p(0), p(1), p(2)],
            ],
        );
        for (name, options) in all_options() {
            let mut sink = VecProofSink::new();
            let out = inprocess_into(&f, options, None, &mut sink).expect("infallible");
            let SatResult::Sat(model) =
                solve_with_native_core(&out.formula).expect("core reports a valid model")
            else {
                panic!("{name}: reduced formula must stay satisfiable");
            };
            let lifted = out.reconstruction.extend(model.values());
            assert_eq!(
                f.evaluate(&lifted),
                Ok(true),
                "{name}: lifted model must satisfy the ORIGINAL formula"
            );
        }
    }

    // --- The shipping schedule (ADR-1810) ---------------------------------

    /// Everything on, as the shipping backend configures it under
    /// `prove_unsat`.
    fn full_schedule() -> InprocessSchedule {
        InprocessSchedule {
            xor_propagate: true,
            xor_propagate_max_clauses: 20_000,
            vivify: true,
            vivify_step_guard: true,
            recording: true,
            ..InprocessSchedule::OFF
        }
    }

    /// A pigeonhole big enough that the search still has work after the passes
    /// have run: 4 pigeons into 3 holes.
    fn pigeonhole_4_3() -> CnfFormula {
        let mut f = CnfFormula::new(12);
        for pigeon in 0..4 {
            f.add_clause(CnfClause::new(vec![
                p(3 * pigeon),
                p(3 * pigeon + 1),
                p(3 * pigeon + 2),
            ]))
            .expect("in range");
        }
        for hole in 0..3 {
            for a in 0..4 {
                for b in (a + 1)..4 {
                    f.add_clause(CnfClause::new(vec![n(3 * a + hole), n(3 * b + hole)]))
                        .expect("in range");
                }
            }
        }
        f
    }

    /// THE property the whole schedule exists to preserve: a refutation of the
    /// formula the search actually ran over lifts, through the link, into a
    /// refutation of the formula the CALLER handed in — across a reduction that
    /// both derived clauses and renumbered variables.
    ///
    /// Three assertions exist to stop the headline one from passing vacuously.
    /// `prefix_len > 0` says the passes actually derived something; a reduction
    /// that changed nothing makes "covers the original" true and meaningless.
    /// A non-empty search proof says the search contributed a refutation rather
    /// than the prefix having refuted the formula on its own, which is a real
    /// vacuity trap on small pigeonholes. `has_renaming` says compaction
    /// actually renumbered, so the lift really had to run.
    #[test]
    fn the_schedules_certificate_covers_the_original_formula() {
        let f = pigeonhole_4_3();
        let mut observer = RecordingObserver::granting(u64::MAX);
        let out = inprocess_scheduled(&f, full_schedule(), None, &mut observer);

        assert!(
            out.link.prefix_len() > 0,
            "the passes must have derived something: {:?}",
            observer.counts
        );
        assert!(
            out.link.has_renaming(),
            "compaction must renumber, or the lift is untested"
        );
        assert!(
            out.link.is_checkable(),
            "no pass may leave the link unusable"
        );

        let ProofSolveOutcome::Unsat(search_proof) = solve_with_drat_proof(&out.formula) else {
            panic!("the reduced formula must still be unsatisfiable");
        };
        assert!(
            !search_proof.is_empty(),
            "the search must contribute steps, or the prefix refuted alone"
        );

        let check = out
            .link
            .check_unsat(&f, &out.formula, &search_proof, usize::MAX);
        assert!(
            check.verified,
            "the concatenation must verify: {:?}",
            check.error
        );
        assert!(
            check.coverage.is_original(),
            "and it must cover the ORIGINAL formula, not the reduced one: {:?}",
            check.coverage
        );
        assert_eq!(
            check.prefix_steps,
            out.link.prefix_len(),
            "every step the passes recorded must be part of the checked proof"
        );
    }

    /// The schedule preserves satisfiability, and a `sat` model of the searched
    /// formula lifts back through `compaction.expand` and then
    /// `reconstruction.extend` — in that order — to a model of the caller's.
    #[test]
    fn a_scheduled_sat_model_replays_against_the_original() {
        let f = formula(
            4,
            &[
                &[p(0), p(1)],
                &[p(2), p(3)],
                &[n(0), n(2)],
                &[n(1), n(3)],
                &[p(0), p(1)],
                &[p(0), p(1), p(2)],
            ],
        );
        let mut observer = RecordingObserver::granting(u64::MAX);
        let out = inprocess_scheduled(&f, full_schedule(), None, &mut observer);
        let SatResult::Sat(model) =
            solve_with_native_core(&out.formula).expect("core reports a valid model")
        else {
            panic!("the reduced formula must stay satisfiable");
        };
        let reduced = out.compaction.expand(model.values());
        let lifted = out.reconstruction.extend(&reduced);
        assert_eq!(
            f.evaluate(&lifted),
            Ok(true),
            "the lifted model must satisfy the ORIGINAL formula"
        );
    }

    /// Recording is keyed on the caller's intent, not on whether a pass ran.
    ///
    /// The point is the pairing: the reduction is the SAME reduction either way
    /// — same reduced formula, same counters — and the only difference is
    /// whether a prefix proportional to the formula was built. Asserting the
    /// empty link alone would pass for a build where the passes had silently
    /// stopped running.
    #[test]
    fn a_non_recording_run_pays_nothing_for_a_prefix_it_will_not_check() {
        let f = pigeonhole_4_3();

        let mut recording_obs = RecordingObserver::granting(u64::MAX);
        let recorded = inprocess_scheduled(&f, full_schedule(), None, &mut recording_obs);

        let quiet_schedule = InprocessSchedule {
            recording: false,
            vivify_step_guard: false,
            ..full_schedule()
        };
        let mut quiet_obs = RecordingObserver::granting(u64::MAX);
        let quiet = inprocess_scheduled(&f, quiet_schedule, None, &mut quiet_obs);

        assert!(
            recorded.link.prefix_len() > 0,
            "the recording arm must actually record"
        );
        assert_eq!(
            quiet.link.prefix_len(),
            0,
            "a non-proof solve must not build a prefix"
        );
        assert_eq!(
            quiet.formula, recorded.formula,
            "recording must not change the reduction it observes"
        );
        assert_eq!(
            quiet_obs.get("bve_variables_eliminated"),
            recording_obs.get("bve_variables_eliminated"),
            "...nor what the passes did"
        );
        assert_eq!(
            quiet_obs.get("inprocess_proof_steps"),
            None,
            "and the prefix counter is absent rather than zero, so a reader can \
             tell 'not recorded' from 'recorded nothing'"
        );
    }

    /// A declined grant means the pass did not run — including through the
    /// schedule, which is the only route the solver takes.
    #[test]
    fn declining_every_grant_leaves_the_clause_set_alone() {
        let f = pigeonhole_4_3();
        let mut observer = NoObserver;
        let out = inprocess_scheduled(&f, InprocessSchedule::OFF, None, &mut observer);
        assert_eq!(
            out.formula.clauses().len(),
            f.clauses().len(),
            "no pass ran, so no clause moved"
        );
        assert_eq!(out.link.prefix_len(), 0);
    }

    /// The per-stage telemetry `span_log` and the cost reports read.
    ///
    /// Each key is checked for a distinct reason: the `*_ms` triple is what
    /// attributes a spend to a stage rather than to "inprocessing"; the
    /// `*_deadline_expired` pair is the only observable that separates "the pass
    /// is expensive" from "the clock cut it off"; and the deadline keys must be
    /// ABSENT with no deadline, so a missing key reads as "truncation was
    /// impossible", never as "did not happen".
    #[test]
    fn the_schedule_emits_the_per_stage_telemetry_its_consumers_read() {
        let f = pigeonhole_4_3();

        let mut undated = RecordingObserver::granting(u64::MAX);
        let _ = inprocess_scheduled(&f, full_schedule(), None, &mut undated);
        for key in [
            "inprocess_literals_before",
            "xor_propagate_ms",
            "subsume_ms",
            "vivify_ms",
            "bve_ms",
            "compact_ms",
            "subsume_work_spent",
            "bve_work_spent",
            "inprocess_literals_after",
            "cnf_inprocessing",
        ] {
            assert!(
                undated.get(key).is_some(),
                "{key} must be recorded; got {:?}",
                undated.counts
            );
        }
        for key in [
            "subsume_deadline_expired",
            "vivify_deadline_expired",
            "bve_deadline_expired",
        ] {
            assert_eq!(
                undated.get(key),
                None,
                "{key} must be ABSENT with no deadline, not zero"
            );
        }

        let mut dated = RecordingObserver::granting(u64::MAX);
        let far = Instant::now() + Duration::from_secs(600);
        let _ = inprocess_scheduled(&f, full_schedule(), Some(far), &mut dated);
        for key in [
            "subsume_deadline_expired",
            "vivify_deadline_expired",
            "bve_deadline_expired",
        ] {
            assert_eq!(
                dated.get(key),
                Some(0.0),
                "{key} must be recorded (and unexpired) under a generous deadline"
            );
        }
    }

    /// Vivification's stage keys, and its step-guard, are gated by their own
    /// flags rather than by the schedule running at all.
    ///
    /// The negative half matters as much as the positive: `preprocess()` has
    /// `vivify: false` while the shipping SMT default is `cnf_vivify: true`, so
    /// a caller that picks an arm by NAME instead of building it from its own
    /// config changes behaviour silently. This test is what makes that visible.
    #[test]
    fn vivification_and_its_guard_are_gated_by_their_own_flags() {
        let f = pigeonhole_4_3();

        let mut on = RecordingObserver::granting(u64::MAX);
        let _ = inprocess_scheduled(&f, full_schedule(), None, &mut on);
        assert!(on.get("vivify_clauses_strengthened").is_some());
        assert_eq!(
            on.get("vivify_drat_step_checked"),
            Some(1.0),
            "the step-guard must run and hold under `prove_unsat`"
        );

        let mut off = RecordingObserver::granting(u64::MAX);
        let no_vivify = InprocessSchedule {
            vivify: false,
            ..full_schedule()
        };
        let _ = inprocess_scheduled(&f, no_vivify, None, &mut off);
        assert!(
            !off.counts.iter().any(|(key, _)| key.starts_with("vivify_")),
            "no vivify_* key may appear with the pass off: {:?}",
            off.counts
        );

        let mut unguarded = RecordingObserver::granting(u64::MAX);
        let no_guard = InprocessSchedule {
            vivify_step_guard: false,
            ..full_schedule()
        };
        let _ = inprocess_scheduled(&f, no_guard, None, &mut unguarded);
        assert_eq!(
            unguarded.get("vivify_drat_step_checked"),
            None,
            "the guard is the flag's, not the pass's"
        );
    }
}
