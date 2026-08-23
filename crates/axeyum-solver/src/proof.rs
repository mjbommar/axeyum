//! Exportable, externally-checkable `unsat` certificates for the pure-Rust
//! `QF_BV` path (ADR-0011/0012 follow-on).
//!
//! [`export_qf_bv_unsat_proof`] bit-blasts a `QF_BV` query to CNF, runs the
//! proof-producing SAT core, and — on `unsat` — returns the CNF in **DIMACS**
//! and the refutation in standard **DRAT**, both as text. The DRAT is
//! self-verified by the in-tree [`axeyum_cnf::check_drat`] before it is
//! returned, and the same `(dimacs, drat)` pair is accepted by external checkers
//! such as `drat-trim`. This makes the trusted clausal core of an `unsat` an
//! auditable artifact a consumer can save and re-check.
//!
//! Scope: this certifies the **clausal layer** (CNF `unsat`). Certifying the
//! bit-blasting reduction itself (term → AIG → CNF) is the future "SMT-level"
//! proof step; for now the reduction provenance is recorded but the machine
//! check covers the DIMACS/DRAT pair.

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use axeyum_bv::{first_unsupported_op, first_unsupported_sort, lower_terms};
use axeyum_cnf::{
    ProofSolveOutcome, check_drat, check_lrat, parse_dimacs, parse_drat, parse_lrat,
    solve_with_drat_proof_within, tseitin_encode, write_drat, write_lrat,
};
use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_rewrite::{
    ArrayElimError, FuncElimError, IntBlastError, blast_integers, eliminate_arrays,
    eliminate_functions, simplify_datatypes,
};

use crate::error::SolverError;

/// A checkable `unsat` certificate: the CNF and its DRAT refutation, both in
/// standard text formats.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsatProof {
    /// The bit-blasted CNF in DIMACS format.
    pub dimacs: String,
    /// The DRAT refutation (verified by `check_drat`, accepted by `drat-trim`).
    pub drat: String,
    /// The **LRAT** refutation: the same proof in the stronger clausal format with
    /// explicit antecedent hints, so it re-checks in *linear* time (follow the
    /// hints) via [`axeyum_cnf::check_lrat`] — no RUP search. `None` when the proof
    /// could not be elaborated to LRAT (e.g. it uses a RAT step, which the current
    /// elaborator does not hint); the DRAT certificate still stands in that case.
    pub lrat: Option<String>,
}

impl UnsatProof {
    /// Independently re-checks this certificate **from its text alone**: parses
    /// the DIMACS formula and the DRAT proof and confirms the refutation derives
    /// the empty clause (RUP+RAT), exactly as an external `drat-trim` run would.
    ///
    /// This is the consumer-side "trusted small checking" entry point — the DRAT
    /// analogue of the full-profile `FarkasCertificate::verify` method:
    /// a saved certificate can be re-validated later with no access to the solver
    /// that produced it. (The exporters already self-check on the way out; this
    /// lets a *consumer* re-check independently.)
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Backend`] if the stored DIMACS or DRAT text cannot
    /// be parsed (a malformed certificate).
    pub fn recheck(&self) -> Result<bool, SolverError> {
        let formula = parse_dimacs(&self.dimacs).map_err(|error| {
            SolverError::Backend(format!("certificate DIMACS unparseable: {error}"))
        })?;
        let proof = parse_drat(&self.drat).map_err(|error| {
            SolverError::Backend(format!("certificate DRAT unparseable: {error}"))
        })?;
        let drat_ok = check_drat(&formula, &proof).map_err(|error| {
            SolverError::Backend(format!("certificate failed to check: {error}"))
        })?;
        // When an LRAT certificate is also present, it must independently confirm
        // the same refutation; a present-but-failing LRAT is a tampered certificate,
        // so the whole certificate is rejected (never silently trusted to the DRAT).
        if let Some(lrat_text) = &self.lrat {
            let lrat = parse_lrat(lrat_text).map_err(|error| {
                SolverError::Backend(format!("certificate LRAT unparseable: {error}"))
            })?;
            let lrat_ok = check_lrat(&formula, &lrat).map_err(|error| {
                SolverError::Backend(format!("certificate LRAT failed to check: {error}"))
            })?;
            return Ok(drat_ok && lrat_ok);
        }
        Ok(drat_ok)
    }

    /// Rechecks the proof and confirms its DIMACS input is exactly the
    /// deterministic bit-blast/Tseitin encoding of `assertions`.
    ///
    /// This binds an otherwise self-contained clausal proof back to its source
    /// Boolean terms. The term-to-CNF reduction remains the same explicit
    /// trusted reduction used by [`export_qf_bv_unsat_proof`].
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] for unsupported terms, encoding failures, or a
    /// malformed proof.
    pub fn recheck_for_bool_terms(
        &self,
        arena: &TermArena,
        assertions: &[TermId],
    ) -> Result<bool, SolverError> {
        for &term in assertions {
            if arena.sort_of(term) != Sort::Bool {
                return Err(SolverError::NonBooleanAssertion(term));
            }
        }
        if let Some((term, op)) = first_unsupported_op(arena, assertions) {
            return Err(SolverError::Unsupported(format!(
                "term #{} uses unsupported pure-Rust BV operator {op:?}",
                term.index()
            )));
        }
        if let Some((term, sort)) = first_unsupported_sort(arena, assertions) {
            return Err(SolverError::Unsupported(format!(
                "term #{} has sort {sort} the pure-Rust BV backend cannot bit-blast",
                term.index()
            )));
        }
        let lowering = lower_terms(arena, assertions)
            .map_err(|error| SolverError::Backend(format!("bit-blasting failed: {error}")))?;
        let roots = lowering
            .roots()
            .iter()
            .map(|root| root.bits()[0])
            .collect::<Vec<_>>();
        let encoding = tseitin_encode(lowering.aig(), &roots)
            .map_err(|error| SolverError::Backend(format!("CNF encoding failed: {error}")))?;
        if encoding.formula().to_dimacs() != self.dimacs {
            return Ok(false);
        }
        self.recheck()
    }

    /// Independently re-checks **only** the LRAT certificate in *linear* time
    /// ([`axeyum_cnf::check_lrat`], following the antecedent hints — no RUP search).
    /// Returns `Ok(None)` when no LRAT certificate is attached.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Backend`] if the stored DIMACS or LRAT text cannot be
    /// parsed.
    pub fn recheck_lrat(&self) -> Result<Option<bool>, SolverError> {
        let Some(lrat_text) = &self.lrat else {
            return Ok(None);
        };
        let formula = parse_dimacs(&self.dimacs).map_err(|error| {
            SolverError::Backend(format!("certificate DIMACS unparseable: {error}"))
        })?;
        let lrat = parse_lrat(lrat_text).map_err(|error| {
            SolverError::Backend(format!("certificate LRAT unparseable: {error}"))
        })?;
        check_lrat(&formula, &lrat).map(Some).map_err(|error| {
            SolverError::Backend(format!("certificate LRAT failed to check: {error}"))
        })
    }
}

/// The outcome of attempting to export an `unsat` proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnsatProofOutcome {
    /// The query is unsatisfiable with a DRAT-checked certificate.
    Proved(UnsatProof),
    /// The query is satisfiable, so there is no `unsat` proof.
    Satisfiable,
    /// The proof core exhausted its conflict budget without deciding.
    Inconclusive,
}

/// Bit-blasts a `QF_BV` conjunction and, if unsatisfiable, returns a
/// DRAT-checked, exportable `unsat` certificate.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if the query is outside the bit-blasted
/// `QF_BV` fragment, [`SolverError::NonBooleanAssertion`] for a non-Boolean
/// assertion, or [`SolverError::Backend`] on an internal encoding failure or a
/// proof that fails to check (a soundness alarm).
pub fn export_qf_bv_unsat_proof(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<UnsatProofOutcome, SolverError> {
    export_qf_bv_unsat_proof_impl(arena, assertions, None)
}

/// Like [`export_qf_bv_unsat_proof`], but the proof-producing SAT search returns
/// [`UnsatProofOutcome::Inconclusive`] when `deadline` expires.
///
/// The deadline only bounds the optional proof search. If it expires, no
/// satisfiability verdict is claimed from the exporter.
///
/// # Errors
///
/// Returns the same errors as [`export_qf_bv_unsat_proof`].
pub fn export_qf_bv_unsat_proof_within(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Result<UnsatProofOutcome, SolverError> {
    export_qf_bv_unsat_proof_impl(arena, assertions, deadline)
}

/// Like [`export_qf_bv_unsat_proof_within`], but the checking stage that runs
/// after the search returns `unsat` is bounded/observed per `check_budget`
/// (see [`CheckBudget`] / [`CheckingProgress`], and
/// [`export_qf_bv_unsat_proof_with_progress`]'s doc for why this exists).
///
/// [`export_qf_bv_unsat_proof_within`] is exactly this function called with
/// [`CheckBudget::default`] — unbounded, unobserved, the previous behaviour.
///
/// # Errors
///
/// Returns the same errors as [`export_qf_bv_unsat_proof`].
pub fn export_qf_bv_unsat_proof_within_with_check_budget(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
    check_budget: CheckBudget<'_>,
) -> Result<UnsatProofOutcome, SolverError> {
    let encoding = qf_bv_cnf_encoding(arena, assertions)?;
    let formula = encoding.formula();
    finish_unsat_proof_outcome_with_check_budget(
        formula,
        solve_with_drat_proof_within(formula, deadline),
        check_budget,
    )
}

fn export_qf_bv_unsat_proof_impl(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Result<UnsatProofOutcome, SolverError> {
    export_qf_bv_unsat_proof_within_with_check_budget(
        arena,
        assertions,
        deadline,
        CheckBudget::default(),
    )
}

/// Like [`export_qf_bv_unsat_proof_within`], but polls `progress` every
/// `progress_interval` conflicts (and once more at the end) during the
/// proof-producing SAT search — the observability hook for a certificate run
/// long enough that elapsed time and RSS are otherwise the only signals
/// available (see [`axeyum_cnf::ProofSearchProgress`]).
///
/// `check_budget` is the SAME kind of observability/bound, but for the stage
/// that runs *after* the search returns `unsat`: [`axeyum_cnf::check_drat`]
/// and [`axeyum_cnf::elaborate_drat_to_lrat`], the checking pass
/// [`finish_unsat_proof_outcome_with_check_budget`] performs to turn a raw
/// refutation into an
/// [`UnsatProof`]. That pass has no bound of its own — the 2026-08 incident
/// motivating this module's checking-progress hooks was exactly this: a
/// search that finished in 24.2 s followed by a check that ran for nearly six
/// hours with zero observable output. Pass [`CheckBudget::default`] to get the
/// previous behaviour back exactly (unbounded, unobserved).
///
/// Same soundness/behaviour as [`export_qf_bv_unsat_proof_within`]: this
/// shares its bit-blast/encode step ([`qf_bv_cnf_encoding`]) and its
/// outcome-to-certificate mapping ([`finish_unsat_proof_outcome_with_check_budget`])
/// verbatim, differing only in which `axeyum_cnf` SAT-search entry point runs —
/// and that entry point's own doc guarantees installing a sink cannot change
/// the search trajectory or the emitted proof. Likewise, `check_budget`'s
/// deadline/step budget/progress sink cannot change what the checking stage
/// ACCEPTS — see `axeyum_cnf::check_drat_streaming_with_limits_and_progress`'s
/// and `axeyum_cnf::elaborate_drat_to_lrat_with_limits_and_progress`'s own
/// no-behaviour-change guarantees, which this relies on rather than re-asserts
/// — only whether/when checking gives up early. A checking stage that gives up
/// early is reported as [`UnsatProofOutcome::Inconclusive`], never as
/// [`UnsatProofOutcome::Proved`]: a timeout is not a pass.
///
/// # Errors
///
/// Returns the same errors as [`export_qf_bv_unsat_proof`].
pub fn export_qf_bv_unsat_proof_with_progress(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
    max_conflicts: usize,
    progress_interval: usize,
    progress: &mut dyn FnMut(&axeyum_cnf::ProofSearchProgress),
    check_budget: CheckBudget<'_>,
) -> Result<UnsatProofOutcome, SolverError> {
    let encoding = qf_bv_cnf_encoding(arena, assertions)?;
    let formula = encoding.formula();
    let outcome = axeyum_cnf::solve_with_drat_proof_with_limits_and_progress(
        formula,
        deadline,
        max_conflicts,
        progress_interval,
        progress,
    );
    finish_unsat_proof_outcome_with_check_budget(formula, outcome, check_budget)
}

/// Bit-blasts `assertions` to a Tseitin `CnfEncoding` — the shared front half
/// of every `export_qf_bv_unsat_proof*` variant (progress-observed or not),
/// so the checks, `lower_terms`, and `tseitin_encode` calls exist exactly
/// once regardless of which SAT-search entry point runs afterward.
fn qf_bv_cnf_encoding(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<axeyum_cnf::CnfEncoding, SolverError> {
    for &term in assertions {
        if arena.sort_of(term) != Sort::Bool {
            return Err(SolverError::NonBooleanAssertion(term));
        }
    }
    if let Some((term, op)) = first_unsupported_op(arena, assertions) {
        return Err(SolverError::Unsupported(format!(
            "term #{} uses unsupported pure-Rust BV operator {op:?}",
            term.index()
        )));
    }
    if let Some((term, sort)) = first_unsupported_sort(arena, assertions) {
        return Err(SolverError::Unsupported(format!(
            "term #{} has sort {sort} the pure-Rust BV backend cannot bit-blast",
            term.index()
        )));
    }

    let lowering = lower_terms(arena, assertions)
        .map_err(|error| SolverError::Backend(format!("bit-blasting failed: {error}")))?;
    let roots = lowering
        .roots()
        .iter()
        .map(|root| root.bits()[0])
        .collect::<Vec<_>>();
    tseitin_encode(lowering.aig(), &roots)
        .map_err(|error| SolverError::Backend(format!("CNF encoding failed: {error}")))
}

/// One observability snapshot from the checking stage that follows a
/// proof-producing search's `unsat` — the checking-side counterpart of
/// [`axeyum_cnf::ProofSearchProgress`] on the search side. Wraps whichever of
/// the two checking sub-stages is currently running: [`axeyum_cnf::check_drat`]
/// re-derives the RUP/RAT refutation the search claims; if that verifies, an
/// independent second pass, [`axeyum_cnf::elaborate_drat_to_lrat`], recovers
/// explicit hints so the certificate can also be re-checked in linear time via
/// [`axeyum_cnf::check_lrat`]. Both are re-scans over the SAME proof and were
/// both found to run for hours with no bound and no output (2026-08 incident:
/// a 24.2 s search followed by a ~6 h checking pass on
/// `neg-fp16-add-monotone-rne.smt2`); this type lets a caller watch — and
/// [`CheckBudget`] lets a caller bound — either one.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CheckingProgress {
    /// A snapshot from the [`axeyum_cnf::check_drat`]-equivalent pass.
    DratCheck(axeyum_cnf::DratCheckProgress),
    /// A snapshot from the [`axeyum_cnf::elaborate_drat_to_lrat`]-equivalent
    /// pass, which only runs when the DRAT check above already verified.
    LratElaborate(axeyum_cnf::LratElaborateProgress),
}

/// Bounds and observability for the checking stage that follows a
/// proof-producing search's `unsat` (see [`CheckingProgress`]).
///
/// `CheckBudget::default()` reproduces the previous, unbounded, unobserved
/// behaviour exactly: `deadline: None`, `max_steps: None`, `progress: None` —
/// so passing it changes nothing about what is accepted or how long checking
/// is allowed to run. That default is also what the internal checking-stage
/// tail (behind `export_qf_bv_unsat_proof_with_progress` /
/// `export_qf_bv_unsat_proof_within_with_check_budget`) uses when no explicit
/// budget is given, which is why installing this type at all is opt-in.
///
/// `deadline` and `max_steps` bound BOTH checking sub-stages independently
/// (each stage gets the SAME deadline and the SAME step budget — they are not
/// summed or split), mirroring how the search itself takes one `deadline` and
/// one `max_conflicts`. Either bound firing on either stage is reported as
/// [`UnsatProofOutcome::Inconclusive`], never [`UnsatProofOutcome::Proved`]: a
/// timeout is not a pass.
pub struct CheckBudget<'a> {
    /// Wall-clock deadline for each checking sub-stage. `None` means
    /// unbounded (the previous behaviour).
    pub deadline: Option<Instant>,
    /// Step budget for each checking sub-stage (DRAT steps for the check
    /// pass, DRAT steps again for the elaboration pass — the two proofs have
    /// the same length). `None` means unbounded (the previous behaviour).
    pub max_steps: Option<usize>,
    /// Cadence, in checked/processed steps, between [`CheckingProgress`]
    /// snapshots. Clamped to at least 1 by the underlying checker; irrelevant
    /// when `progress` is `None`.
    pub progress_interval: usize,
    /// Observability sink. `None` (the default) costs nothing beyond an
    /// `Option::is_none` check per step in the underlying checker — see
    /// `axeyum_cnf::check_drat_streaming_with_limits_and_progress`'s and
    /// `axeyum_cnf::elaborate_drat_to_lrat_with_limits_and_progress`'s own
    /// zero-cost-when-absent guarantees.
    pub progress: Option<&'a mut dyn FnMut(&CheckingProgress)>,
}

impl Default for CheckBudget<'_> {
    fn default() -> Self {
        Self {
            deadline: None,
            max_steps: None,
            progress_interval: 1,
            progress: None,
        }
    }
}

/// Maps a [`ProofSolveOutcome`] on `formula` to an [`UnsatProofOutcome`],
/// including the LRAT elaboration and the DRAT self-check — the shared tail
/// of every `export_qf_bv_unsat_proof*` variant, so this soundness-critical
/// logic exists exactly once regardless of which SAT-search entry point (with
/// or without a progress sink) produced `outcome`. The checking stage
/// ([`axeyum_cnf::check_drat`] then, if that verifies,
/// [`axeyum_cnf::elaborate_drat_to_lrat`]) is bounded and observed per
/// `check_budget` (see [`CheckBudget`] / [`CheckingProgress`]).
///
/// [`CheckBudget::default`] reproduces the previous unbounded, unobserved
/// behaviour exactly — "checking never declines to finish, however long that
/// takes" — so every existing call site keeps that behaviour by passing it.
///
/// A checking-stage bound firing (on either sub-stage) is reported as
/// [`UnsatProofOutcome::Inconclusive`] — the SAME outcome a search-stage
/// timeout gets. This loses the distinction "the search decided this in
/// seconds; only checking could not finish in time", but that distinction is
/// still recoverable from the `CheckingProgress` stream itself (a search that
/// finished is followed by search-side silence and then a run of checking
/// snapshots), and collapsing the two here means every existing match on
/// [`UnsatProofOutcome`] stays exhaustive without a new variant to update at
/// each of its call sites.
#[allow(clippy::similar_names)] // drat_sink_fn/lrat_sink_fn mirror the two checking sub-stages
fn finish_unsat_proof_outcome_with_check_budget(
    formula: &axeyum_cnf::CnfFormula,
    outcome: ProofSolveOutcome,
    mut check_budget: CheckBudget<'_>,
) -> Result<UnsatProofOutcome, SolverError> {
    match outcome {
        ProofSolveOutcome::Sat(_) => Ok(UnsatProofOutcome::Satisfiable),
        ProofSolveOutcome::ResourceOut | ProofSolveOutcome::Interrupted => {
            Ok(UnsatProofOutcome::Inconclusive)
        }
        ProofSolveOutcome::Unsat(proof) => {
            let want_progress = check_budget.progress.is_some();
            let mut drat_sink_fn = |snapshot: &axeyum_cnf::DratCheckProgress| {
                if let Some(sink) = check_budget.progress.as_mut() {
                    sink(&CheckingProgress::DratCheck(*snapshot));
                }
            };
            let drat_sink: Option<&mut dyn FnMut(&axeyum_cnf::DratCheckProgress)> = if want_progress
            {
                Some(&mut drat_sink_fn)
            } else {
                None
            };
            let drat_outcome = axeyum_cnf::check_drat_with_limits_and_progress(
                formula,
                &proof,
                check_budget.deadline,
                check_budget.max_steps,
                check_budget.progress_interval,
                drat_sink,
            )
            .map_err(|error| {
                SolverError::Backend(format!("exported unsat proof failed to check: {error}"))
            })?;
            match drat_outcome {
                axeyum_cnf::DratCheckOutcome::Verified(true) => {
                    // Elaborate the (RUP) DRAT proof to LRAT for linear re-checking; if
                    // a step is not RUP-elaboratable (RAT), the elaboration is bounded
                    // out, or the deadline passes, keep DRAT-only. The LRAT, when
                    // present, is self-checked here so a stored certificate cannot carry
                    // a bad LRAT past the exporter.
                    let mut lrat_sink_fn = |snapshot: &axeyum_cnf::LratElaborateProgress| {
                        if let Some(sink) = check_budget.progress.as_mut() {
                            sink(&CheckingProgress::LratElaborate(*snapshot));
                        }
                    };
                    let lrat_sink: Option<&mut dyn FnMut(&axeyum_cnf::LratElaborateProgress)> =
                        if want_progress {
                            Some(&mut lrat_sink_fn)
                        } else {
                            None
                        };
                    let lrat = match axeyum_cnf::elaborate_drat_to_lrat_with_limits_and_progress(
                        formula,
                        &proof,
                        check_budget.deadline,
                        check_budget.max_steps,
                        check_budget.progress_interval,
                        lrat_sink,
                    ) {
                        Ok(axeyum_cnf::LratElaborateOutcome::Elaborated(steps))
                            if matches!(check_lrat(formula, &steps), Ok(true)) =>
                        {
                            Some(write_lrat(&steps))
                        }
                        _ => None,
                    };
                    Ok(UnsatProofOutcome::Proved(UnsatProof {
                        dimacs: formula.to_dimacs(),
                        drat: write_drat(&proof),
                        lrat,
                    }))
                }
                axeyum_cnf::DratCheckOutcome::Verified(false) => Err(SolverError::Backend(
                    "exported unsat proof did not derive the empty clause".to_owned(),
                )),
                // A timeout is not a pass: neither bound firing is ever mapped to
                // `Proved`. The search already found a refutation, but it is
                // unverified, so this is reported exactly like a search-stage
                // timeout — undecided, not wrong, never certified.
                axeyum_cnf::DratCheckOutcome::ResourceOut
                | axeyum_cnf::DratCheckOutcome::Interrupted => Ok(UnsatProofOutcome::Inconclusive),
            }
        }
    }
}

/// Like [`export_qf_bv_unsat_proof`] but for **`QF_ABV`** (arrays): eagerly
/// eliminates `select`/`store` to `QF_BV` (read-over-write + Ackermann,
/// ADR-0010), then exports the DRAT-checked certificate of the eliminated query.
///
/// The returned `(dimacs, drat)` is an externally-checkable (`drat-trim`) proof
/// that the *array-eliminated* CNF is `unsat`. The original `QF_ABV` query is
/// then `unsat` by the soundness of the elimination (an
/// equisatisfiability-preserving transform, ADR-0010 — the same one the
/// validated `check_with_array_elimination` solve path uses, and which a `sat`
/// model independently replays through). So the assurance is: **machine-checked
/// at the clausal layer, modulo the trusted (and replay-validatable) array
/// elimination** — strictly stronger than a bare uncertified `unsat`. Certifying
/// the elimination step itself is future SMT-level proof work.
///
/// Takes `&mut` arena because elimination introduces terms.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for constructs outside `QF_ABV`,
/// [`SolverError::NonBooleanAssertion`], or [`SolverError::Backend`] on an
/// encoding failure or a proof that fails to check.
pub fn export_qf_abv_unsat_proof(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<UnsatProofOutcome, SolverError> {
    export_qf_abv_unsat_proof_within(arena, assertions, None)
}

/// Like [`export_qf_abv_unsat_proof`], but the final BV proof search is bounded
/// by `deadline`.
///
/// # Errors
///
/// Returns the same errors as [`export_qf_abv_unsat_proof`].
pub fn export_qf_abv_unsat_proof_within(
    arena: &mut TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Result<UnsatProofOutcome, SolverError> {
    let elimination = eliminate_arrays(arena, assertions).map_err(|error| match error {
        ArrayElimError::Unsupported(what) => SolverError::Unsupported(what),
        ArrayElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    })?;
    let eliminated = elimination.assertions().to_vec();
    export_qf_bv_unsat_proof_within(arena, &eliminated, deadline)
}

/// Checkable `unsat` certificate for the combined **`QF_AUFBV`** fragment
/// (arrays *and* uninterpreted functions over bit-vectors — the realistic
/// verification/symbolic-execution shape: symbolic memory plus uninterpreted
/// summaries). Eliminates arrays then functions, then exports the `QF_BV`
/// certificate. Same assurance shape as the single-reduction exporters
/// (clausal-layer checked, modulo the trusted reductions).
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for constructs outside `QF_AUFBV`,
/// [`SolverError::NonBooleanAssertion`], or [`SolverError::Backend`] on an
/// encoding failure or a proof that fails to check.
pub fn export_qf_aufbv_unsat_proof(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<UnsatProofOutcome, SolverError> {
    export_qf_aufbv_unsat_proof_within(arena, assertions, None)
}

/// Like [`export_qf_aufbv_unsat_proof`], but the final BV proof search is bounded
/// by `deadline`.
///
/// # Errors
///
/// Returns the same errors as [`export_qf_aufbv_unsat_proof`].
pub fn export_qf_aufbv_unsat_proof_within(
    arena: &mut TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Result<UnsatProofOutcome, SolverError> {
    let array_elim = eliminate_arrays(arena, assertions).map_err(|error| match error {
        ArrayElimError::Unsupported(what) => SolverError::Unsupported(what),
        ArrayElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    })?;
    let after_arrays = array_elim.assertions().to_vec();
    let func_elim = eliminate_functions(arena, &after_arrays).map_err(|error| match error {
        FuncElimError::Unsupported(what) => SolverError::Unsupported(what),
        FuncElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    })?;
    let eliminated = func_elim.assertions().to_vec();
    export_qf_bv_unsat_proof_within(arena, &eliminated, deadline)
}

/// Like [`export_qf_bv_unsat_proof`] but for **`QF_UFBV`** (uninterpreted
/// functions over bit-vectors): Ackermann-reduces function applications to
/// fresh variables plus functional-consistency constraints (ADR-0013), then
/// exports the DRAT-checked certificate of the reduced `QF_BV` query.
///
/// Same assurance shape as [`export_qf_abv_unsat_proof`]: machine-checked at the
/// clausal layer, modulo the trusted (replay-validatable) Ackermann reduction.
/// Takes `&mut` arena because the reduction introduces terms.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for constructs outside `QF_UFBV`,
/// [`SolverError::NonBooleanAssertion`], or [`SolverError::Backend`] on an
/// encoding failure or a proof that fails to check.
pub fn export_qf_uf_unsat_proof(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<UnsatProofOutcome, SolverError> {
    let elimination = eliminate_functions(arena, assertions).map_err(|error| match error {
        FuncElimError::Unsupported(what) => SolverError::Unsupported(what),
        FuncElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    })?;
    let eliminated = elimination.assertions().to_vec();
    export_qf_bv_unsat_proof(arena, &eliminated)
}

/// Checkable `unsat` certificate for **bounded `QF_LIA`**: bit-blasts integers
/// to `BitVec(int_width)` (ADR-0014) and exports the DRAT-checked certificate of
/// the resulting `QF_BV` query. The certificate refutes the query *at the chosen
/// bound* (the bound is part of the claim). If a constant does not fit
/// `int_width`, returns [`UnsatProofOutcome::Inconclusive`] (widen the bound).
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for non-`QF_LIA`/BV constructs,
/// [`SolverError::NonBooleanAssertion`], or [`SolverError::Backend`] on an
/// invalid width / encoding failure / a proof that fails to check.
pub fn export_qf_lia_unsat_proof(
    arena: &mut TermArena,
    assertions: &[TermId],
    int_width: u32,
) -> Result<UnsatProofOutcome, SolverError> {
    let blasting = match blast_integers(arena, assertions, int_width) {
        Ok(blasting) => blasting,
        Err(IntBlastError::ConstantOutOfRange { .. }) => {
            return Ok(UnsatProofOutcome::Inconclusive); // bound too small to bit-blast
        }
        Err(IntBlastError::InvalidWidth(width)) => {
            return Err(SolverError::Backend(format!(
                "invalid integer bit-blast width {width}"
            )));
        }
        // No finite bit-vector encoding (e.g. `int.pow2`): no bit-blast proof here.
        Err(IntBlastError::UnsupportedOp(_)) => return Ok(UnsatProofOutcome::Inconclusive),
        Err(IntBlastError::Ir(inner)) => return Err(SolverError::Backend(inner.to_string())),
    };
    // Fail-closed against restricting guards: when the blast added any
    // no-overflow (faithful-product) side-constraints, the resulting `QF_BV`
    // query is a *strict restriction* of the original (it prunes wrapping
    // products to steer the `sat` search). A DRAT refutation of that restricted
    // query therefore does NOT establish `unsat` of the original integer
    // formula — exporting it would be a wrong `unsat` proof. So we decline to a
    // sound `Inconclusive` rather than certify a refutation we cannot transfer.
    if blasting.restricting_constraints() > 0 {
        return Ok(UnsatProofOutcome::Inconclusive);
    }
    let eliminated = blasting.assertions().to_vec();
    export_qf_bv_unsat_proof(arena, &eliminated)
}

/// Checkable `unsat` certificate for **datatypes** over bit-vectors: folds
/// `select`/`is`/equality over explicit constructors ([`simplify_datatypes`],
/// ADR-0022) and exports the DRAT-checked certificate of the resulting `QF_BV`
/// query. Works when the datatypes fully fold away; a query left with free
/// datatype variables (not bit-blastable) is a clean [`SolverError::Unsupported`].
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for residual datatype constructs,
/// [`SolverError::NonBooleanAssertion`], or [`SolverError::Backend`] on an
/// encoding failure or a proof that fails to check.
pub fn export_datatype_unsat_proof(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<UnsatProofOutcome, SolverError> {
    let simplified =
        simplify_datatypes(arena, assertions).map_err(|e| SolverError::Backend(e.to_string()))?;
    export_qf_bv_unsat_proof(arena, &simplified)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unsat_proof_rechecks_and_detects_tampering() {
        // x = 0 ∧ x = 1 over BV8 is unsatisfiable.
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a = arena.eq(x, zero).unwrap();
        let b = arena.eq(x, one).unwrap();

        let UnsatProofOutcome::Proved(proof) = export_qf_bv_unsat_proof(&arena, &[a, b]).unwrap()
        else {
            panic!("x=0 ∧ x=1 must be unsat with a proof");
        };
        // The exported certificate re-checks independently from its text alone.
        assert!(proof.recheck().unwrap());

        // An LRAT certificate is attached and re-checks in linear time (hints) on
        // its own.
        assert_eq!(
            proof.recheck_lrat().unwrap(),
            Some(true),
            "the exported certificate must carry a linearly-checkable LRAT proof"
        );

        // Corrupting the DRAT (drop its final empty-clause line) must fail the
        // re-check rather than pass — the checker is not fooled.
        let mut broken = proof.clone();
        broken.drat = broken
            .drat
            .lines()
            .filter(|line| line.trim() != "0")
            .collect::<Vec<_>>()
            .join("\n");
        // Either it no longer derives the empty clause (Ok(false)) or the text is
        // now unparseable (Err); both are a rejected certificate, never Ok(true).
        assert!(!matches!(broken.recheck(), Ok(true)));

        // Tampering with the LRAT alone (drop its last hint line) is likewise
        // caught: `recheck` cross-checks the LRAT and rejects the certificate.
        let mut lrat_broken = proof.clone();
        if let Some(text) = lrat_broken.lrat.take() {
            let mut lines: Vec<&str> = text.lines().collect();
            lines.pop(); // drop the final (empty-clause) addition line
            lrat_broken.lrat = Some(lines.join("\n"));
            assert!(
                !matches!(lrat_broken.recheck(), Ok(true)),
                "a tampered LRAT must fail the combined re-check"
            );
        }
    }

    // --- checking-stage progress / bounding (`CheckBudget`) -----------------

    fn contradictory_bv_assertions() -> (TermArena, Vec<TermId>) {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a = arena.eq(x, zero).unwrap();
        let b = arena.eq(x, one).unwrap();
        (arena, vec![a, b])
    }

    #[test]
    fn check_budget_default_matches_the_unbounded_export() {
        let (arena, assertions) = contradictory_bv_assertions();
        let plain = export_qf_bv_unsat_proof(&arena, &assertions).unwrap();
        let budgeted = export_qf_bv_unsat_proof_within_with_check_budget(
            &arena,
            &assertions,
            None,
            CheckBudget::default(),
        )
        .unwrap();
        assert_eq!(
            plain, budgeted,
            "CheckBudget::default() must reproduce the unbounded export exactly"
        );
    }

    #[test]
    fn an_expired_check_deadline_yields_inconclusive_never_proved() {
        let (arena, assertions) = contradictory_bv_assertions();
        let expired = Instant::now()
            .checked_sub(std::time::Duration::from_secs(1))
            .expect("now is well past the epoch");
        let outcome = export_qf_bv_unsat_proof_within_with_check_budget(
            &arena,
            &assertions,
            None,
            CheckBudget {
                deadline: Some(expired),
                ..CheckBudget::default()
            },
        )
        .expect("a checking-stage timeout is an outcome, not an error");
        assert_eq!(
            outcome,
            UnsatProofOutcome::Inconclusive,
            "an expired checking deadline must never be reported as Proved — \
             a timeout is not a pass"
        );
    }

    #[test]
    fn a_zero_check_step_budget_yields_inconclusive_never_proved() {
        let (arena, assertions) = contradictory_bv_assertions();
        let outcome = export_qf_bv_unsat_proof_within_with_check_budget(
            &arena,
            &assertions,
            None,
            CheckBudget {
                max_steps: Some(0),
                ..CheckBudget::default()
            },
        )
        .expect("a checking-stage resource bound is an outcome, not an error");
        assert_eq!(
            outcome,
            UnsatProofOutcome::Inconclusive,
            "a checking step budget of 0 must never be reported as Proved"
        );
    }

    #[test]
    fn checking_progress_sink_fires_and_does_not_change_the_outcome() {
        let (arena, assertions) = contradictory_bv_assertions();
        let plain = export_qf_bv_unsat_proof(&arena, &assertions).unwrap();

        let mut events: Vec<CheckingProgress> = Vec::new();
        let mut record = |event: &CheckingProgress| events.push(*event);
        let outcome = export_qf_bv_unsat_proof_within_with_check_budget(
            &arena,
            &assertions,
            None,
            CheckBudget {
                progress_interval: 1,
                progress: Some(&mut record),
                ..CheckBudget::default()
            },
        )
        .unwrap();
        assert_eq!(
            plain, outcome,
            "installing a checking-progress sink must not change the outcome"
        );
        assert!(
            events
                .iter()
                .any(|event| matches!(event, CheckingProgress::DratCheck(_))),
            "the DRAT-check sub-stage must have reported at least one snapshot"
        );
        assert!(
            events
                .iter()
                .any(|event| matches!(event, CheckingProgress::LratElaborate(_))),
            "the elaboration sub-stage must have reported at least one snapshot \
             (the DRAT check verified, so elaboration must have run)"
        );
    }
}
