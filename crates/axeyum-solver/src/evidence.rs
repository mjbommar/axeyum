//! Self-checking evidence envelopes (ADR-0005 follow-through).
//!
//! [`Evidence`] is a result paired with the artifact that justifies it, and a
//! single [`Evidence::check`] that **re-validates it independently** of the
//! solver that produced it — the "trusted small checking" identity made
//! consumer-facing:
//!
//! - `sat` carries a [`Model`]; `check` replays it through the ground evaluator
//!   against the original assertions.
//! - `unsat` carries an optional [`UnsatProof`] (DIMACS + DRAT); `check`
//!   re-parses and re-runs the trusted [`axeyum_cnf::check_drat`] kernel. A
//!   `None` proof means the result came from the (lower-assurance) adapter
//!   without a DRAT certificate, and is documented as such.
//! - `QF_LRA` `unsat` carries a [`FarkasCertificate`]; `check` re-runs the
//!   independent [`FarkasCertificate::verify`] (the exact-arithmetic dual of the
//!   DRAT route).
//! - `unknown` carries the reason and checks vacuously.
//!
//! [`produce_qf_bv_evidence`] runs the pure-Rust `QF_BV` pipeline and
//! [`produce_lra_evidence`] runs the exact-rational `QF_LRA` pipeline; each
//! packages the outcome as self-checking evidence.

use std::time::Duration;

use axeyum_cnf::{check_drat, parse_dimacs, parse_drat};
use axeyum_ir::{TermArena, TermId, Value, eval};

use crate::backend::{CheckResult, SolverBackend, SolverConfig, SolverError, UnknownReason};
use crate::dpll_t::{LraDpllOutcome, LraDpllRefutation, certify_lra_dpll_unsat};
use crate::lra::{FarkasCertificate, lra_farkas_certificate};
use crate::model::Model;
use crate::proof::{UnsatProof, UnsatProofOutcome, export_qf_bv_unsat_proof};
use crate::sat_bv_backend::SatBvBackend;

/// Version of the executable semantics (the `axeyum-ir` ground evaluator) the
/// evidence was produced and is checkable against. Bump when evaluator
/// semantics change so older evidence is not silently re-interpreted (ADR-0005).
pub const SEMANTICS_VERSION: &str = "1";

/// Versioned provenance for a produced [`Evidence`]: enough to reproduce the run
/// and interpret the evidence later (ADR-0005). Determinism is a public promise,
/// so the SAT path needs no recorded seed; the resource config is recorded
/// because it changes which queries return `unknown`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Provenance {
    /// Executable-semantics version ([`SEMANTICS_VERSION`]).
    pub semantics_version: &'static str,
    /// The deciding backend's capability name (encoder + SAT adapter identity).
    pub backend: String,
    /// Number of asserted formulas decided.
    pub assertion_count: usize,
    /// Wall-clock budget in force, if any.
    pub timeout: Option<Duration>,
    /// Deterministic resource budget in force, if any.
    pub resource_limit: Option<u64>,
    /// Translation node budget in force, if any.
    pub node_budget: Option<u64>,
    /// CNF variable / clause budgets in force, if any.
    pub cnf_variable_budget: Option<u64>,
    /// CNF clause budget in force, if any.
    pub cnf_clause_budget: Option<u64>,
    /// Whether `unsat` was required to carry a checked DRAT proof.
    pub prove_unsat: bool,
}

impl Provenance {
    fn for_query(config: &SolverConfig, backend: String, assertion_count: usize) -> Self {
        Self {
            semantics_version: SEMANTICS_VERSION,
            backend,
            assertion_count,
            timeout: config.timeout,
            resource_limit: config.resource_limit,
            node_budget: config.node_budget,
            cnf_variable_budget: config.cnf_variable_budget,
            cnf_clause_budget: config.cnf_clause_budget,
            prove_unsat: config.prove_unsat,
        }
    }
}

/// A produced [`Evidence`] together with its versioned [`Provenance`].
#[derive(Debug, Clone)]
pub struct EvidenceReport {
    /// The result and its checkable justification.
    pub evidence: Evidence,
    /// How and against what version the evidence was produced.
    pub provenance: Provenance,
}

/// A decided (or undecided) result together with its checkable justification.
#[derive(Debug, Clone)]
pub enum Evidence {
    /// Satisfiable: a model whose replay against the query is the evidence.
    Sat(Model),
    /// Unsatisfiable: a DRAT certificate over the bit-blasted CNF, or `None`
    /// when only a lower-assurance adapter result is available.
    Unsat(Option<UnsatProof>),
    /// Unsatisfiable (`QF_LRA`): a Farkas refutation over the exact-rational
    /// constraints, whose [`FarkasCertificate::verify`] is the evidence.
    UnsatFarkas(FarkasCertificate),
    /// Unsatisfiable (Boolean-structured pure-real `QF_LRA`): a lazy-SMT
    /// refutation (skeleton + Farkas-certified theory lemmas) whose
    /// [`LraDpllRefutation::verify`] is the evidence.
    UnsatLraDpll(LraDpllRefutation),
    /// Undecided, with the classified reason.
    Unknown(UnknownReason),
}

impl Evidence {
    /// Independently re-validates this evidence against the original
    /// `assertions`. Returns `true` when the evidence holds up.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Backend`] if a `sat` replay evaluates to a
    /// non-Boolean (an internal invariant violation) or a stored certificate
    /// fails to re-parse.
    pub fn check(&self, arena: &TermArena, assertions: &[TermId]) -> Result<bool, SolverError> {
        match self {
            Evidence::Sat(model) => {
                let assignment = model.to_assignment();
                for &assertion in assertions {
                    match eval(arena, assertion, &assignment) {
                        Ok(Value::Bool(true)) => {}
                        Ok(Value::Bool(false)) => return Ok(false),
                        Ok(value) => {
                            return Err(SolverError::Backend(format!(
                                "sat evidence replay: assertion #{} is non-Boolean {value}",
                                assertion.index()
                            )));
                        }
                        Err(error) => {
                            return Err(SolverError::Backend(format!(
                                "sat evidence replay: assertion #{} failed to evaluate: {error}",
                                assertion.index()
                            )));
                        }
                    }
                }
                Ok(true)
            }
            Evidence::Unsat(Some(proof)) => {
                let formula = parse_dimacs(&proof.dimacs).map_err(|error| {
                    SolverError::Backend(format!("unsat evidence DIMACS re-parse failed: {error}"))
                })?;
                let steps = parse_drat(&proof.drat).map_err(|error| {
                    SolverError::Backend(format!("unsat evidence DRAT re-parse failed: {error}"))
                })?;
                check_drat(&formula, &steps).map_err(|error| {
                    SolverError::Backend(format!("unsat evidence DRAT re-check failed: {error}"))
                })
            }
            Evidence::UnsatFarkas(certificate) => Ok(certificate.verify()),
            Evidence::UnsatLraDpll(refutation) => refutation.verify(arena),
            // No DRAT certificate (adapter-only `unsat`) or `unknown`: nothing to
            // independently re-check.
            Evidence::Unsat(None) | Evidence::Unknown(_) => Ok(true),
        }
    }

    /// Whether this evidence carries an independently checkable certificate (a
    /// `sat` model, a DRAT `unsat` proof, or a `QF_LRA` Farkas/lazy-SMT
    /// refutation).
    pub fn is_certified(&self) -> bool {
        matches!(
            self,
            Evidence::Sat(_)
                | Evidence::Unsat(Some(_))
                | Evidence::UnsatFarkas(_)
                | Evidence::UnsatLraDpll(_)
        )
    }
}

/// Runs the pure-Rust `QF_BV` pipeline on `assertions` and packages the outcome
/// as a self-checking [`EvidenceReport`]: a `sat` model, a DRAT-checked `unsat`
/// certificate (or `None` if the proof core was inconclusive), or `unknown`,
/// each with versioned [`Provenance`].
///
/// # Errors
///
/// Returns [`SolverError`] from the backend or proof export, including a
/// soundness alarm if the backend and proof core disagree.
pub fn produce_qf_bv_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<EvidenceReport, SolverError> {
    let mut backend = SatBvBackend::new();
    let provenance = Provenance::for_query(config, backend.capabilities().name, assertions.len());
    let evidence = match backend.check(arena, assertions, config)? {
        CheckResult::Sat(model) => Evidence::Sat(model),
        CheckResult::Unknown(reason) => Evidence::Unknown(reason),
        CheckResult::Unsat => match export_qf_bv_unsat_proof(arena, assertions)? {
            UnsatProofOutcome::Proved(proof) => Evidence::Unsat(Some(proof)),
            UnsatProofOutcome::Inconclusive => Evidence::Unsat(None),
            UnsatProofOutcome::Satisfiable => {
                return Err(SolverError::Backend(
                    "soundness alarm: backend reported unsat but the proof core found a model"
                        .to_owned(),
                ));
            }
        },
    };
    Ok(EvidenceReport {
        evidence,
        provenance,
    })
}

/// Runs the exact-rational conjunctive `QF_LRA` pipeline on `assertions` and
/// packages the outcome as a self-checking [`EvidenceReport`]: a `sat` model, a
/// Farkas-certified `unsat` (or `None` for the degenerate literally-`false`
/// case), or — never, for this total procedure — `unknown`.
///
/// The Fourier–Motzkin path honors no resource budgets, so the [`Provenance`]
/// records only the semantics version, backend identity, and assertion count;
/// budget fields are `None`.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if an assertion is outside conjunctive
/// linear real arithmetic, or [`SolverError::Backend`] on a `sat` replay failure
/// or a Farkas self-check failure (procedure-bug soundness alarms).
pub fn produce_lra_evidence(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<EvidenceReport, SolverError> {
    let provenance = Provenance {
        semantics_version: SEMANTICS_VERSION,
        backend: "lra-fourier-motzkin-farkas".to_owned(),
        assertion_count: assertions.len(),
        timeout: None,
        resource_limit: None,
        node_budget: None,
        cnf_variable_budget: None,
        cnf_clause_budget: None,
        prove_unsat: true,
    };
    let evidence = match crate::lra::check_with_lra(arena, assertions)? {
        CheckResult::Sat(model) => Evidence::Sat(model),
        CheckResult::Unknown(reason) => Evidence::Unknown(reason),
        CheckResult::Unsat => match lra_farkas_certificate(arena, assertions)? {
            Some(certificate) => Evidence::UnsatFarkas(certificate),
            // `unsat` with no Farkas certificate is the degenerate
            // literally-`false` assertion case: there is nothing linear to
            // certify, so it is recorded as a (lower-assurance) bare `unsat`.
            None => Evidence::Unsat(None),
        },
    };
    Ok(EvidenceReport {
        evidence,
        provenance,
    })
}

/// Runs the lazy-SMT pure-real `QF_LRA` pipeline on `assertions` (arbitrary
/// Boolean structure over real order atoms) and packages the outcome as a
/// self-checking [`EvidenceReport`]: a `sat` model, an `unsat` backed by a
/// self-checked [`LraDpllRefutation`], or a classified `unknown` (including when
/// the refutation has too many Boolean symbols to certify by enumeration).
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if the query carries non-real,
/// non-Boolean content, or [`SolverError::Backend`] on a `sat` replay failure or
/// a refutation self-check failure (procedure-bug soundness alarms).
pub fn produce_lra_dpll_evidence(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<EvidenceReport, SolverError> {
    let provenance = Provenance {
        semantics_version: SEMANTICS_VERSION,
        backend: "lra-dpll-farkas-enumeration".to_owned(),
        assertion_count: assertions.len(),
        timeout: config.timeout,
        resource_limit: config.resource_limit,
        node_budget: config.node_budget,
        cnf_variable_budget: config.cnf_variable_budget,
        cnf_clause_budget: config.cnf_clause_budget,
        prove_unsat: true,
    };
    let evidence = match certify_lra_dpll_unsat(arena, assertions, config)? {
        LraDpllOutcome::Sat(model) => Evidence::Sat(model),
        LraDpllOutcome::Unsat(refutation) => Evidence::UnsatLraDpll(refutation),
        LraDpllOutcome::Unknown(reason) => Evidence::Unknown(reason),
    };
    Ok(EvidenceReport {
        evidence,
        provenance,
    })
}
