//! Exportable, externally-checkable `unsat` certificates for the pure-Rust
//! `QF_BV` path (ADR-0011/0012 follow-on).
//!
//! [`export_qf_bv_unsat_proof`] bit-blasts a `QF_BV` query to CNF, runs the
//! proof-producing SAT core, and — on `unsat` — returns the CNF in **DIMACS**
//! and the refutation in standard **DRAT**, both as text, normally beside an
//! **LRAT** with explicit antecedent hints. The refutation is self-verified
//! before it is returned, and the same `(dimacs, drat)` pair is accepted by
//! external checkers such as `drat-trim`. This makes the trusted clausal core of
//! an `unsat` an auditable artifact a consumer can save and re-check.
//!
//! *Which* checker discharges that verification is ADR-0613: normally the core
//! is elaborated to LRAT by the backward engine (untrusted, fast) and the hints
//! are verified by [`axeyum_cnf::check_lrat`] (trusted, search-free, linear);
//! when that route declines — a RAT lemma, or a checking budget too small for a
//! stage that cannot be interrupted — the forward reference
//! [`axeyum_cnf::check_drat`] runs instead, exactly as before. Either way the
//! accepting authority is a checker small enough to audit by reading; the
//! difference is only whether it has to *search* for the refutation or is handed
//! it.
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
    LratCertifyOutcome, ProofSolveOutcome, certify_unsat_via_lrat, check_drat, check_drat_backward,
    check_lrat, parse_dimacs, parse_drat, parse_lrat, solve_with_drat_proof_within, tseitin_encode,
    write_drat, write_lrat,
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
    /// The DRAT refutation, self-verified before this certificate was returned
    /// and accepted by external `drat-trim`.
    ///
    /// *Which* in-tree checker verified it depends on the route taken
    /// (ADR-0613): normally the backward core-first engine, whose emitted hints
    /// `check_lrat` then confirmed; on the fallback route, the forward reference
    /// `check_drat`. The two agree on every proof the reference accepts
    /// (ADR-0382); the backward route additionally tolerates unjustified dead
    /// weight *outside* the refutation's core, which is `drat-trim`'s own
    /// contract, so a certificate from either route is externally checkable.
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
    ///
    /// # Which checker decides, and why it is not the fast one (ADR-0613)
    ///
    /// When an LRAT certificate is present it is the **accepting authority**:
    /// [`axeyum_cnf::check_lrat`] follows its hints against the stored DIMACS with
    /// no search at all, in time linear in the proof. The DRAT text is then
    /// re-checked too — with [`axeyum_cnf::check_drat_backward`], which is
    /// ~66x faster than the forward reference (ADR-0382) — but that check appears
    /// **only in conjunctive position**. It can turn an accept into a reject and
    /// never the reverse, so however wrong the backward engine might be, it cannot
    /// make this method accept a certificate `check_lrat` did not accept. That is
    /// what lets the cost come out of the re-check without any trust going into
    /// the machinery that made it cheap.
    ///
    /// The conjunct is not decoration: it is what catches a certificate whose
    /// LRAT is intact and whose published DRAT — the artifact an external
    /// `drat-trim` would read — has been tampered with.
    ///
    /// With no LRAT present (a RAT proof, which this workspace's own core does
    /// not emit) there is nothing to follow hints for, and the forward reference
    /// checker [`axeyum_cnf::check_drat`] decides, exactly as before.
    pub fn recheck(&self) -> Result<bool, SolverError> {
        let formula = parse_dimacs(&self.dimacs).map_err(|error| {
            SolverError::Backend(format!("certificate DIMACS unparseable: {error}"))
        })?;
        let proof = parse_drat(&self.drat).map_err(|error| {
            SolverError::Backend(format!("certificate DRAT unparseable: {error}"))
        })?;
        // When an LRAT certificate is present, it must independently confirm the
        // refutation; a present-but-failing LRAT is a tampered certificate, so the
        // whole certificate is rejected (never silently trusted to the DRAT).
        if let Some(lrat_text) = &self.lrat {
            let lrat = parse_lrat(lrat_text).map_err(|error| {
                SolverError::Backend(format!("certificate LRAT unparseable: {error}"))
            })?;
            let lrat_ok = check_lrat(&formula, &lrat).map_err(|error| {
                SolverError::Backend(format!("certificate LRAT failed to check: {error}"))
            })?;
            let drat_ok = check_drat_backward(&formula, &proof).map_err(|error| {
                SolverError::Backend(format!("certificate failed to check: {error}"))
            })?;
            return Ok(lrat_ok && drat_ok);
        }
        check_drat(&formula, &proof)
            .map_err(|error| SolverError::Backend(format!("certificate failed to check: {error}")))
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
/// `finish_unsat_proof_outcome_with_check_budget` performs to turn a raw
/// refutation into an
/// [`UnsatProof`]. That pass has no bound of its own — the 2026-08 incident
/// motivating this module's checking-progress hooks was exactly this: a
/// search that finished in 24.2 s followed by a check that ran for nearly six
/// hours with zero observable output. Pass [`CheckBudget::default`] to get the
/// previous behaviour back exactly (unbounded, unobserved).
///
/// Same soundness/behaviour as [`export_qf_bv_unsat_proof_within`]: this
/// shares its bit-blast/encode step (`qf_bv_cnf_encoding`) and its
/// outcome-to-certificate mapping (`finish_unsat_proof_outcome_with_check_budget`)
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
    /// A snapshot from the backward LRAT certification stage
    /// ([`axeyum_cnf::certify_unsat_via_lrat`], ADR-0613) — the route that runs
    /// *instead of* the two above whenever the checking budget admits it.
    BackwardLratCertify(BackwardCertifyProgress),
}

/// A snapshot from the backward LRAT certification stage (ADR-0613).
///
/// The backward engine walks the proof in reverse and is not step-interruptible,
/// so unlike the two forward sub-stages this reports exactly **twice**: once as
/// the stage opens and once as it closes. Two samples is not a progress bar, and
/// it is still the whole difference between "which stage is running" and
/// silence — the question the 2026-08 `neg-fp16-add-monotone-rne` incident could
/// not answer, where a 24 s search was followed by hours of unattributed
/// checking.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BackwardCertifyProgress {
    /// DRAT steps handed to the stage.
    pub steps_total: usize,
    /// Wall-clock elapsed inside this stage so far.
    pub elapsed: std::time::Duration,
    /// `false` on the opening snapshot, `true` on the closing one.
    pub finished: bool,
    /// Whether the stage certified the refutation. Meaningless until
    /// `finished`; `false` on a decline, which is **not** a statement that the
    /// proof is bad (see [`axeyum_cnf::LratCertifyOutcome`]).
    pub certified: bool,
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
/// or without a progress sink) produced `outcome`.
///
/// # Two checking routes, one trusted base (ADR-0613)
///
/// The **fast route** runs first whenever `check_budget` admits it
/// ([`budget_admits_backward_certify`]): [`axeyum_cnf::certify_unsat_via_lrat`]
/// elaborates the proof's core with the backward engine and has
/// [`axeyum_cnf::check_lrat`] verify the resulting hints. A `Certified` there is
/// discharged by `check_lrat` — small, search-free, linear — so `Proved` on this
/// route rests on no more trust than `Proved` on the old one, and considerably
/// less machinery than the forward RUP search it replaces.
///
/// The **reference route** — [`axeyum_cnf::check_drat`] then, if that verifies,
/// [`axeyum_cnf::elaborate_drat_to_lrat`] — is unchanged and runs whenever the
/// fast route was refused by the budget or declined (a RAT core lemma, or hints
/// `check_lrat` would not accept). It is bounded and observed per `check_budget`
/// (see [`CheckBudget`] / [`CheckingProgress`]).
///
/// A decline is not a verdict, so falling through is not "trying again until one
/// of them says yes": the fast route has *no opinion* when it declines, and the
/// reference route is then the only route that has spoken.
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
/// Whether `budget` admits the backward LRAT certification stage (ADR-0613) for
/// a proof of `steps` DRAT steps.
///
/// That stage walks the proof in reverse and cannot be interrupted part-way, so
/// it may only be entered when the budget can accommodate it **whole**:
///
/// - an already-expired `deadline` refuses it, which is what keeps
///   "a timeout is not a pass" true — an expired budget still reaches the
///   bounded forward route and reports [`UnsatProofOutcome::Inconclusive`];
/// - a `max_steps` smaller than the proof refuses it, because the stage cannot
///   stop at `max_steps` and report partial progress the way the forward
///   checkers can.
///
/// A live deadline admits it, and the stage is then not itself
/// deadline-interruptible — so a caller's deadline can be overshot by at most
/// this stage's cost. That is a strict improvement on the route it replaces,
/// which is the same kind of uninterruptible and measured at ~66x the work
/// (ADR-0382); and an overshoot that certifies is a real verification, never a
/// timeout promoted to a pass.
fn budget_admits_backward_certify(budget: &CheckBudget<'_>, steps: usize) -> bool {
    if budget
        .deadline
        .is_some_and(|deadline| Instant::now() >= deadline)
    {
        return false;
    }
    budget.max_steps.is_none_or(|max| max >= steps)
}

/// Runs the backward LRAT certification stage (ADR-0613) over `proof`, reporting
/// its opening and closing snapshots to `check_budget`'s sink.
///
/// `Some(certificate)` means [`axeyum_cnf::check_lrat`] followed the emitted
/// hints against `formula` and reached the empty clause — `formula` is
/// unsatisfiable, on the authority of that checker alone. `None` means the route
/// **declined**, which says nothing whatever about `proof`: the caller must fall
/// back to the forward reference route rather than treat it as a failure.
///
/// The caller checks [`budget_admits_backward_certify`] first; this function
/// does not, because the stage is uninterruptible and there is nothing useful it
/// could do with a budget half way through.
fn backward_lrat_certificate(
    formula: &axeyum_cnf::CnfFormula,
    proof: &[axeyum_cnf::DratStep],
    check_budget: &mut CheckBudget<'_>,
) -> Option<UnsatProof> {
    let started = Instant::now();
    let steps_total = proof.len();
    let mut report = |elapsed, finished, certified| {
        if let Some(sink) = check_budget.progress.as_mut() {
            sink(&CheckingProgress::BackwardLratCertify(
                BackwardCertifyProgress {
                    steps_total,
                    elapsed,
                    finished,
                    certified,
                },
            ));
        }
    };
    report(std::time::Duration::ZERO, false, false);
    let outcome = certify_unsat_via_lrat(formula, proof);
    let certified = matches!(outcome, LratCertifyOutcome::Certified(_));
    report(started.elapsed(), true, certified);
    match outcome {
        LratCertifyOutcome::Certified(steps) => Some(UnsatProof {
            dimacs: formula.to_dimacs(),
            drat: write_drat(proof),
            lrat: Some(write_lrat(&steps)),
        }),
        LratCertifyOutcome::Declined(_) => None,
    }
}

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
            // FAST ROUTE (ADR-0613), tried first whenever the budget admits it.
            //
            // `certify_unsat_via_lrat` elaborates the proof's CORE to LRAT with
            // the backward engine (untrusted) and has `check_lrat` (trusted,
            // search-free) verify the hints. A `Certified` here is discharged by
            // `check_lrat` alone, so this is a change of SPEED, not of trusted
            // base — see that function's own doc for the argument.
            //
            // A `Declined` says nothing about `proof`, so it falls through to
            // the forward reference route below rather than reporting a failure.
            if budget_admits_backward_certify(&check_budget, proof.len())
                && let Some(certificate) =
                    backward_lrat_certificate(formula, &proof, &mut check_budget)
            {
                return Ok(UnsatProofOutcome::Proved(certificate));
            }

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

    /// The certificate's LRAT is the accepting authority, and the DRAT re-check
    /// is a rejecting-only conjunct (ADR-0613). This pins the conjunct: an
    /// intact LRAT beside a DRAT whose refutation has been removed must be
    /// REJECTED, even though `check_lrat` alone would accept.
    ///
    /// Without the conjunct a consumer would be told the certificate holds while
    /// the artifact an external `drat-trim` reads does not check — the one
    /// disagreement between our answer and an outside checker's that this
    /// project cannot afford.
    #[test]
    fn an_intact_lrat_does_not_rescue_a_gutted_drat() {
        let (arena, assertions) = contradictory_bv_assertions();
        let UnsatProofOutcome::Proved(proof) =
            export_qf_bv_unsat_proof(&arena, &assertions).unwrap()
        else {
            panic!("x=0 ∧ x=1 must be unsat with a proof");
        };
        assert!(
            proof.recheck().unwrap(),
            "positive control: intact certificate"
        );
        assert_eq!(
            proof.recheck_lrat().unwrap(),
            Some(true),
            "the fixture needs an LRAT that verifies on its own"
        );

        // Strip every empty-clause line from the DRAT. The LRAT is untouched, so
        // `check_lrat` still says `Ok(true)`; only the conjunct can catch this.
        let mut gutted = proof.clone();
        gutted.drat = gutted
            .drat
            .lines()
            .filter(|line| line.trim() != "0")
            .collect::<Vec<_>>()
            .join("\n");
        assert_ne!(
            gutted.drat, proof.drat,
            "the fixture must have changed the DRAT"
        );
        assert_eq!(
            gutted.recheck_lrat().unwrap(),
            Some(true),
            "the LRAT half must still pass — otherwise this test is not \
             exercising the DRAT conjunct at all"
        );
        assert!(
            !matches!(gutted.recheck(), Ok(true)),
            "a certificate whose published DRAT no longer refutes must be \
             rejected, however good its LRAT is"
        );
    }

    /// The reverse pairing: a DRAT that still checks beside an LRAT whose hints
    /// have been forged must also be rejected. `check_lrat` is the accepting
    /// authority, so nothing may accept around it.
    #[test]
    fn a_valid_drat_does_not_rescue_a_forged_lrat() {
        let (arena, assertions) = contradictory_bv_assertions();
        let UnsatProofOutcome::Proved(proof) =
            export_qf_bv_unsat_proof(&arena, &assertions).unwrap()
        else {
            panic!("x=0 ∧ x=1 must be unsat with a proof");
        };
        let lrat_text = proof.lrat.clone().expect("the exporter attaches LRAT");
        // Rewrite every hint id to one that cannot exist. The DRAT is untouched.
        let forged: String = lrat_text
            .lines()
            .map(|line| {
                let Some((head, _hints)) = line.rsplit_once(" 0 ") else {
                    return line.to_owned();
                };
                format!("{head} 0 999999 0")
            })
            .collect::<Vec<_>>()
            .join("\n");
        let mut tampered = proof.clone();
        tampered.lrat = Some(forged);
        assert!(
            !matches!(tampered.recheck(), Ok(true)),
            "forged LRAT hints must be rejected — the trusted checker follows \
             hints, so an unfollowable hint is a rejected certificate"
        );
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
        // With no bound installed the budget admits the backward route
        // (ADR-0613), so the observability comes from that stage. It reports
        // exactly twice — opening and closing — and the closing snapshot must
        // say it certified, since this query is unsat with a RUP-only proof.
        let backward: Vec<_> = events
            .iter()
            .filter_map(|event| match event {
                CheckingProgress::BackwardLratCertify(snapshot) => Some(*snapshot),
                _ => None,
            })
            .collect();
        assert_eq!(
            backward.len(),
            2,
            "the backward certify stage must report exactly one opening and one \
             closing snapshot, got {backward:?}"
        );
        assert!(!backward[0].finished, "the first snapshot opens the stage");
        assert!(backward[1].finished, "the second snapshot closes it");
        assert!(
            backward[1].certified,
            "an unsat query with a RUP-only proof must certify through LRAT"
        );
        assert_eq!(
            backward[0].steps_total, backward[1].steps_total,
            "both snapshots describe the same proof"
        );
    }

    /// The reference (forward) route keeps its own observability: install a step
    /// budget too small for the non-interruptible backward stage but large
    /// enough for the bounded forward one, and both forward sub-stages must
    /// still report.
    ///
    /// Without this the `CheckingProgress::DratCheck` / `LratElaborate` arms
    /// would have no live test at all once the backward route became the
    /// default, and a regression in the fallback's observability — the exact
    /// thing the 2026-08 fp16 incident cost — would go unnoticed.
    #[test]
    fn the_reference_route_still_reports_both_of_its_sub_stages() {
        let (arena, assertions) = contradictory_bv_assertions();
        let UnsatProofOutcome::Proved(reference) =
            export_qf_bv_unsat_proof(&arena, &assertions).unwrap()
        else {
            panic!("x=0 ∧ x=1 must be unsat with a proof");
        };
        let steps = parse_drat(&reference.drat).expect("the exported DRAT parses");
        assert!(!steps.is_empty(), "the proof must have steps to bound");

        let mut events: Vec<CheckingProgress> = Vec::new();
        let mut record = |event: &CheckingProgress| events.push(*event);
        let outcome = export_qf_bv_unsat_proof_within_with_check_budget(
            &arena,
            &assertions,
            None,
            CheckBudget {
                // One step short of the proof: refuses the whole-or-nothing
                // backward stage, admits the step-bounded forward one.
                max_steps: Some(steps.len() - 1),
                progress_interval: 1,
                progress: Some(&mut record),
                ..CheckBudget::default()
            },
        )
        .unwrap();
        assert!(
            !events
                .iter()
                .any(|event| matches!(event, CheckingProgress::BackwardLratCertify(_))),
            "a step budget smaller than the proof must refuse the backward stage"
        );
        assert!(
            events
                .iter()
                .any(|event| matches!(event, CheckingProgress::DratCheck(_))),
            "the DRAT-check sub-stage must have reported at least one snapshot"
        );
        // Whether elaboration also runs depends on whether the bounded DRAT
        // check verified inside its budget; when it did, elaboration must have
        // reported too.
        if outcome != UnsatProofOutcome::Inconclusive {
            assert!(
                events
                    .iter()
                    .any(|event| matches!(event, CheckingProgress::LratElaborate(_))),
                "the DRAT check verified, so elaboration must have run and reported"
            );
        }
    }
}
