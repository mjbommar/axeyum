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

use crate::bve::{BveOptions, BveStats, Reconstruction, eliminate_variables_within_recorded};
use crate::simplify::{SubsumeStats, simplify_within_recorded};
use crate::vivify::{VivifyOptions, VivifyStats, vivify_within};
use crate::{CnfFormula, DratSink, DratStep, ProofSinkError};

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
    /// The shipping SMT path enables it by default with inprocessing
    /// (`SolverConfig::cnf_vivify`). See
    /// `docs/research/03-measurements/inprocessing-admission-2026-09-08.md`.
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
        let (reduced, subsume_stats) =
            simplify_within_recorded(&current, deadline, Some(&mut steps));
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CnfClause, CnfFormula, CnfLit, CnfVar, SatResult, VecProofSink, check_drat,
        solve_with_native_core,
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
}
