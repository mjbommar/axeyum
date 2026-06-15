//! Self-checking evidence envelopes (ADR-0005 follow-through).
//!
//! [`Evidence`] is a result paired with the artifact that justifies it, and a
//! single [`Evidence::check`] that **re-validates it independently** of the
//! solver that produced it — the "trusted small checking" identity made
//! consumer-facing:
//!
//! - `sat` carries a [`Model`]; `check` replays it through the ground evaluator
//!   against the original assertions.
//! - small `QF_BV` `unsat` carries a **term-level** certificate (the strongest:
//!   exhaustive evaluation over the finite symbol domain, trusting only the
//!   evaluator — not the bit-blaster, CNF encoder, or SAT solver); `check`
//!   re-enumerates.
//! - larger `QF_BV` `unsat` carries an optional [`UnsatProof`] (DIMACS + DRAT);
//!   `check` re-parses and re-runs the trusted [`axeyum_cnf::check_drat`] kernel.
//!   A `None` proof means the result came from the (lower-assurance) adapter
//!   without a DRAT certificate, and is documented as such.
//! - `QF_LRA` `unsat` carries a [`FarkasCertificate`]; `check` re-runs the
//!   independent [`FarkasCertificate::verify`] (the exact-arithmetic dual of the
//!   DRAT route).
//! - Boolean-structured pure-real `unsat` carries an [`LraDpllRefutation`];
//!   `check` re-runs [`LraDpllRefutation::verify`].
//! - `unknown` carries the reason and checks vacuously.
//!
//! [`produce_qf_bv_evidence`], [`produce_lra_evidence`], and
//! [`produce_lra_dpll_evidence`] run the per-theory pipelines, and
//! [`produce_evidence`] is the unified front door that routes any supported query
//! to the producer with the strongest available certificate (mirroring
//! [`crate::solve`]).

use std::collections::BTreeSet;
use std::time::Duration;

use axeyum_cnf::{check_drat, parse_dimacs, parse_drat};
use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode, Value, eval};

use crate::auto::solve;
use crate::backend::{CheckResult, SolverBackend, SolverConfig, SolverError, UnknownReason};
use crate::certify::{CertifyOutcome, certify_qf_bv_by_enumeration};
use crate::dpll_t::{LraDpllOutcome, LraDpllRefutation, certify_lra_dpll_unsat};
use crate::lra::{FarkasCertificate, lra_farkas_certificate};
use crate::model::Model;
use crate::proof::{UnsatProof, UnsatProofOutcome, export_qf_bv_unsat_proof};
use crate::sat_bv_backend::SatBvBackend;
use crate::trust::{TrustId, TrustStep};

/// Version of the executable semantics (the `axeyum-ir` ground evaluator) the
/// evidence was produced and is checkable against. Bump when evaluator
/// semantics change so older evidence is not silently re-interpreted (ADR-0005).
///
/// This is the **trusted checker's** version — distinct from the untrusted
/// search-pipeline layer versions in [`LayerVersions`].
pub const SEMANTICS_VERSION: &str = "1";

/// Versions of the **untrusted search-pipeline** layers, recorded in
/// [`Provenance`] so a replay failure can be localized to whichever layer
/// changed rather than being mysterious (architecture review #8; ADR-0005). The
/// trusted checker's version is [`Provenance::semantics_version`] separately —
/// these layers produce the result; the evaluator checks it.
///
/// Bump a field when that layer's *observable* behavior changes (a new rewrite
/// rule, a different bit encoding, a changed CNF scheme, a swapped SAT adapter,
/// an FP-circuit change, a parser grammar change, or a different lift-map
/// convention). Centralized here for one place to bump; a future refinement can
/// source each from its own crate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LayerVersions {
    /// `axeyum-rewrite` ruleset / canonicalizer version.
    pub rewrite: &'static str,
    /// `axeyum-bv` term→AIG bit-blaster version.
    pub bitblaster: &'static str,
    /// `axeyum-cnf` Tseitin/DIMACS encoder version.
    pub cnf: &'static str,
    /// SAT adapter identity/behavior version (e.g. `rustsat-batsat`).
    pub sat_adapter: &'static str,
    /// `axeyum-fp` floating-point circuit semantics version.
    pub fp_semantics: &'static str,
    /// `axeyum-smtlib` front-end (parser/writer) version.
    pub parser: &'static str,
    /// Model lift-map / replay-map convention version.
    pub lift_map: &'static str,
}

impl LayerVersions {
    /// The versions of the layers as currently built.
    pub const CURRENT: LayerVersions = LayerVersions {
        rewrite: "1",
        bitblaster: "1",
        cnf: "1",
        sat_adapter: "rustsat-batsat",
        fp_semantics: "1",
        parser: "1",
        lift_map: "1",
    };
}

/// Combined-symbol-width budget for attaching a reduction-free term-level `unsat`
/// certificate (2^20 = ~1M enumerated assignments). Above this the DRAT clausal
/// proof is used instead.
const TERM_LEVEL_CERT_BITS: u32 = 20;

/// Versioned provenance for a produced [`Evidence`]: enough to reproduce the run
/// and interpret the evidence later (ADR-0005). Determinism is a public promise,
/// so the SAT path needs no recorded seed; the resource config is recorded
/// because it changes which queries return `unknown`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Provenance {
    /// Executable-semantics version ([`SEMANTICS_VERSION`]) — the trusted checker.
    pub semantics_version: &'static str,
    /// Versions of the untrusted search-pipeline layers (review #8), so a replay
    /// failure localizes to the layer that changed.
    pub layers: LayerVersions,
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
            layers: LayerVersions::CURRENT,
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
    /// The trusted/certified reductions this result depended on, in canonical
    /// [`crate::trust::ALL_TRUST_IDS`] order (deduplicated). Empty for `sat`
    /// (replay), `unknown`, and bare `unsat` without a certificate. This is the
    /// trust ledger made per-result (P3.0): a consumer can read exactly which
    /// reductions back an `unsat` and whether this run certified each.
    pub trusted_steps: Vec<TrustStep>,
}

/// Builds a deterministic, deduplicated, canonically-ordered trust-step list from
/// `(id, certified_this_run)` pairs. Iterating [`crate::trust::ALL_TRUST_IDS`]
/// guarantees source order regardless of insertion order (no hash-map leak).
fn trust_steps(steps: &[(TrustId, bool)]) -> Vec<TrustStep> {
    crate::trust::ALL_TRUST_IDS
        .iter()
        .filter_map(|&id| {
            steps
                .iter()
                .find(|(sid, _)| *sid == id)
                .map(|&(_, certified)| TrustStep { id, certified })
        })
        .collect()
}

/// A decided (or undecided) result together with its checkable justification.
#[derive(Debug, Clone)]
pub enum Evidence {
    /// Satisfiable: a model whose replay against the query is the evidence.
    Sat(Model),
    /// Unsatisfiable: a DRAT certificate over the bit-blasted CNF, or `None`
    /// when only a lower-assurance adapter result is available.
    Unsat(Option<UnsatProof>),
    /// Unsatisfiable, certified **at the term level** by exhaustive evaluation
    /// over the finite symbol domain — the strongest `QF_BV` `unsat` evidence,
    /// trusting neither the bit-blaster, CNF encoder, nor SAT solver (only the
    /// `axeyum-ir` evaluator). Carries the number of cases checked and the bit
    /// budget, so `check` can re-run the same enumeration.
    UnsatTermLevel {
        /// Number of assignments exhaustively evaluated.
        cases: u64,
        /// The combined-symbol-width budget the certification used.
        max_total_bits: u32,
    },
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
            Evidence::UnsatTermLevel { max_total_bits, .. } => {
                // Re-run the reduction-free enumeration; it must again find no
                // satisfying assignment.
                match certify_qf_bv_by_enumeration(arena, assertions, *max_total_bits)? {
                    CertifyOutcome::CertifiedUnsat { .. } => Ok(true),
                    CertifyOutcome::Satisfiable(_) => Ok(false),
                    CertifyOutcome::DomainTooLarge { total_bits } => {
                        Err(SolverError::Backend(format!(
                            "term-level unsat evidence: domain {total_bits} bits exceeds the \
                             recorded budget {max_total_bits}"
                        )))
                    }
                }
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
                | Evidence::UnsatTermLevel { .. }
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
    let (evidence, trusted_steps) = match backend.check(arena, assertions, config)? {
        CheckResult::Sat(model) => (Evidence::Sat(model), Vec::new()),
        CheckResult::Unknown(reason) => (Evidence::Unknown(reason), Vec::new()),
        CheckResult::Unsat => {
            // Prefer a reduction-free term-level certificate when the instance is
            // small enough to enumerate: it trusts only the evaluator, closing the
            // term↔CNF gap entirely. Fall back to the DRAT clausal proof otherwise.
            match certify_qf_bv_by_enumeration(arena, assertions, TERM_LEVEL_CERT_BITS) {
                Ok(CertifyOutcome::CertifiedUnsat { cases }) => (
                    Evidence::UnsatTermLevel {
                        cases,
                        max_total_bits: TERM_LEVEL_CERT_BITS,
                    },
                    // Trusts only the evaluator — no reduction trust.
                    trust_steps(&[(TrustId::TermLevelEnum, true)]),
                ),
                Ok(CertifyOutcome::Satisfiable(_)) => {
                    return Err(SolverError::Backend(
                        "soundness alarm: backend reported unsat but term-level enumeration \
                         found a model"
                            .to_owned(),
                    ));
                }
                // Too large to enumerate (or enumeration unsupported): use DRAT.
                Ok(CertifyOutcome::DomainTooLarge { .. }) | Err(_) => {
                    match export_qf_bv_unsat_proof(arena, assertions)? {
                        // Bit-blast is recorded (a miter route exists, but this
                        // plain DRAT export does not run it → certified:false);
                        // Tseitin + the SAT refutation are DRAT-checked here.
                        UnsatProofOutcome::Proved(proof) => (
                            Evidence::Unsat(Some(proof)),
                            trust_steps(&[
                                (TrustId::BitBlast, false),
                                (TrustId::Tseitin, true),
                                (TrustId::SatRefutation, true),
                            ]),
                        ),
                        UnsatProofOutcome::Inconclusive => (
                            Evidence::Unsat(None),
                            trust_steps(&[
                                (TrustId::BitBlast, false),
                                (TrustId::Tseitin, true),
                                (TrustId::SatRefutation, false),
                            ]),
                        ),
                        UnsatProofOutcome::Satisfiable => {
                            return Err(SolverError::Backend(
                                "soundness alarm: backend reported unsat but the proof core \
                                 found a model"
                                    .to_owned(),
                            ));
                        }
                    }
                }
            }
        }
    };
    Ok(EvidenceReport {
        evidence,
        provenance,
        trusted_steps,
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
        layers: LayerVersions::CURRENT,
        backend: "lra-fourier-motzkin-farkas".to_owned(),
        assertion_count: assertions.len(),
        timeout: None,
        resource_limit: None,
        node_budget: None,
        cnf_variable_budget: None,
        cnf_clause_budget: None,
        prove_unsat: true,
    };
    let (evidence, trusted_steps) = match crate::lra::check_with_lra(arena, assertions)? {
        CheckResult::Sat(model) => (Evidence::Sat(model), Vec::new()),
        CheckResult::Unknown(reason) => (Evidence::Unknown(reason), Vec::new()),
        CheckResult::Unsat => match lra_farkas_certificate(arena, assertions)? {
            // Exact-rational Farkas: no bit-blast, no Tseitin — certified.
            Some(certificate) => (
                Evidence::UnsatFarkas(certificate),
                trust_steps(&[(TrustId::Farkas, true)]),
            ),
            // `unsat` with no Farkas certificate is the degenerate
            // literally-`false` assertion case: there is nothing linear to
            // certify, so it is recorded as a (lower-assurance) bare `unsat`.
            None => (Evidence::Unsat(None), Vec::new()),
        },
    };
    Ok(EvidenceReport {
        evidence,
        provenance,
        trusted_steps,
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
        layers: LayerVersions::CURRENT,
        backend: "lra-dpll-farkas-enumeration".to_owned(),
        assertion_count: assertions.len(),
        timeout: config.timeout,
        resource_limit: config.resource_limit,
        node_budget: config.node_budget,
        cnf_variable_budget: config.cnf_variable_budget,
        cnf_clause_budget: config.cnf_clause_budget,
        prove_unsat: true,
    };
    let (evidence, trusted_steps) = match certify_lra_dpll_unsat(arena, assertions, config)? {
        LraDpllOutcome::Sat(model) => (Evidence::Sat(model), Vec::new()),
        LraDpllOutcome::Unsat(refutation) => (
            Evidence::UnsatLraDpll(refutation),
            trust_steps(&[(TrustId::LraDpll, true)]),
        ),
        LraDpllOutcome::Unknown(reason) => (Evidence::Unknown(reason), Vec::new()),
    };
    Ok(EvidenceReport {
        evidence,
        provenance,
        trusted_steps,
    })
}

/// The unified evidence front door: decides any supported query with [`solve`]'s
/// routing and packages a self-checking [`EvidenceReport`].
///
/// It dispatches to the producer with the strongest available certificate:
///
/// - **pure `QF_BV`/Boolean** → [`produce_qf_bv_evidence`] (DRAT `unsat` proof);
/// - **pure linear real arithmetic** → [`produce_lra_dpll_evidence`]
///   (Farkas/lazy-SMT refutation);
/// - **everything else supported** (arrays, uninterpreted functions, bounded
///   integers, mixed real + bit-blasted, quantifiers) → [`solve`], whose `sat`
///   model is replay-certified; its `unsat` is recorded as a *bare*
///   `Evidence::Unsat(None)` because a transferable proof artifact for those
///   reductions is not built yet (the honest, documented trust gap — see the
///   open "bit-blast-reduction certification" track).
///
/// In every branch a `sat` result is replay-checkable and the result re-validates
/// through a single [`Evidence::check`].
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for queries outside the supported
/// fragment, or [`SolverError`] from the chosen engine (a failed self-check is a
/// [`SolverError::Backend`] soundness alarm).
pub fn produce_evidence(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<EvidenceReport, SolverError> {
    match evidence_route(arena, assertions) {
        // Pure QF_BV/Boolean: the bit-blast → DRAT route gives a checkable `unsat`.
        EvidenceRoute::QfBv => return produce_qf_bv_evidence(arena, assertions, config),
        // Pure linear real arithmetic (any Boolean structure): the lazy-SMT /
        // Farkas refutation route.
        EvidenceRoute::PureReal => return produce_lra_dpll_evidence(arena, assertions, config),
        EvidenceRoute::Other => {}
    }

    // Everything else supported: decide with the unified engine. `sat` is
    // replay-certified; `unsat` over a BV-reducible fragment (arrays/UF/datatypes)
    // now carries a re-checkable DRAT certificate of the reduced CNF (clausal
    // layer, modulo the trusted reduction); fragments without a reduction-to-BV
    // certificate (e.g. integers/real/nonlinear) still record a bare `unsat`.
    let provenance = Provenance {
        semantics_version: SEMANTICS_VERSION,
        layers: LayerVersions::CURRENT,
        backend: "auto-solve".to_owned(),
        assertion_count: assertions.len(),
        timeout: config.timeout,
        resource_limit: config.resource_limit,
        node_budget: config.node_budget,
        cnf_variable_budget: config.cnf_variable_budget,
        cnf_clause_budget: config.cnf_clause_budget,
        prove_unsat: false,
    };
    let (evidence, trusted_steps) = match solve(arena, assertions, config)? {
        CheckResult::Sat(model) => (Evidence::Sat(model), Vec::new()),
        CheckResult::Unsat => {
            let (cert, steps) = reduction_unsat_certificate(arena, assertions);
            (Evidence::Unsat(cert), steps)
        }
        CheckResult::Unknown(reason) => (Evidence::Unknown(reason), Vec::new()),
    };
    Ok(EvidenceReport {
        evidence,
        provenance,
        trusted_steps,
    })
}

/// Best-effort re-checkable certificate for an `unsat` over a BV-reducible
/// fragment: tries the arrays+UF reduction, then the datatype reduction, and
/// returns the first DRAT-checked proof together with the [`TrustStep`]s that
/// certificate depended on (the reduction trust holes it went through plus the
/// certified clausal layer). `None` (and no steps) for fragments without a
/// reduction-to-BV certificate (integers/real/nonlinear) — a sound bare `unsat`.
/// The underlying engine already decided `unsat`; this only adds an artifact.
fn reduction_unsat_certificate(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> (Option<UnsatProof>, Vec<TrustStep>) {
    use crate::proof::{export_datatype_unsat_proof, export_qf_aufbv_unsat_proof};

    let (has_array, has_func, has_datatype) = reduction_fragment_flags(arena, assertions);

    // Arrays + uninterpreted functions → BV. Only the reductions that actually
    // fire (present in the fragment) are recorded as trust holes.
    if let Ok(UnsatProofOutcome::Proved(proof)) = export_qf_aufbv_unsat_proof(arena, assertions) {
        let mut steps: Vec<(TrustId, bool)> = Vec::new();
        if has_array {
            steps.push((TrustId::ArrayElim, false));
        }
        if has_func {
            steps.push((TrustId::Ackermann, false));
        }
        steps.push((TrustId::BitBlast, false));
        steps.push((TrustId::Tseitin, true));
        steps.push((TrustId::SatRefutation, true));
        return (Some(proof), trust_steps(&steps));
    }
    // Datatypes folded over constructors → BV.
    if let Ok(UnsatProofOutcome::Proved(proof)) = export_datatype_unsat_proof(arena, assertions) {
        let mut steps: Vec<(TrustId, bool)> = Vec::new();
        if has_datatype {
            steps.push((TrustId::DatatypeElim, false));
        }
        steps.push((TrustId::BitBlast, false));
        steps.push((TrustId::Tseitin, true));
        steps.push((TrustId::SatRefutation, true));
        return (Some(proof), trust_steps(&steps));
    }
    (None, Vec::new())
}

/// The presence of the reductions whose trust the `Other` route can incur:
/// arrays, uninterpreted-function applications, and datatypes. One traversal.
fn reduction_fragment_flags(arena: &TermArena, assertions: &[TermId]) -> (bool, bool, bool) {
    let (mut has_array, mut has_func, mut has_datatype) = (false, false, false);
    let mut seen = BTreeSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.sort_of(term) {
            Sort::Array { .. } => has_array = true,
            Sort::Datatype(_) => has_datatype = true,
            _ => {}
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, Op::Apply(_)) {
                has_func = true;
            }
            stack.extend(args.iter().copied());
        }
    }
    (has_array, has_func, has_datatype)
}

/// The outcome of a [`prove`] attempt — the proving arm of the north star.
#[derive(Debug, Clone)]
pub enum ProofOutcome {
    /// The goal follows from the hypotheses. The [`EvidenceReport`] is the
    /// refutation of `hypotheses ∧ ¬goal`; for a certified theory it has already
    /// been re-checked, so `Proved` means an independently verified proof.
    /// Boxed because the report (model/proof + provenance) is much larger than
    /// the other variants.
    Proved(Box<EvidenceReport>),
    /// The goal does **not** follow: `countermodel` satisfies the hypotheses
    /// while falsifying the goal (it is replay-checked against `hypotheses ∧
    /// ¬goal`).
    Disproved(Model),
    /// Could not be decided, with the classified reason.
    Unknown(UnknownReason),
}

/// Proves that `goal` follows from `hypotheses` by **refuting its negation**:
/// it decides `hypotheses ∧ ¬goal` via [`produce_evidence`] and turns the
/// outcome into a [`ProofOutcome`]. An `unsat` (the negation is impossible) is a
/// proof; a `sat` is a countermodel; `unknown` is inconclusive.
///
/// When the refutation carries a certificate, it is **re-checked here before
/// `Proved` is returned**, so `Proved` is a verified proof (a failed check is a
/// [`SolverError::Backend`] soundness alarm). This is the consumer-facing
/// "proving" interface over the checkable-`unsat` machinery: untrusted search,
/// trusted small checking.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if `goal` is non-Boolean or the query is
/// outside the supported fragment, or [`SolverError`] from the engine; a failed
/// proof re-check is a [`SolverError::Backend`].
pub fn prove(
    arena: &mut TermArena,
    hypotheses: &[TermId],
    goal: TermId,
    config: &SolverConfig,
) -> Result<ProofOutcome, SolverError> {
    let negated_goal = arena.not(goal)?;
    let mut query: Vec<TermId> = hypotheses.to_vec();
    query.push(negated_goal);

    let report = produce_evidence(arena, &query, config)?;
    match &report.evidence {
        Evidence::Sat(model) => Ok(ProofOutcome::Disproved(model.clone())),
        Evidence::Unknown(reason) => Ok(ProofOutcome::Unknown(reason.clone())),
        // Any `unsat` evidence variant means the negation is impossible: a proof.
        // Re-check the certificate before declaring `Proved`.
        Evidence::Unsat(_)
        | Evidence::UnsatTermLevel { .. }
        | Evidence::UnsatFarkas(_)
        | Evidence::UnsatLraDpll(_) => {
            if !report.evidence.check(arena, &query)? {
                return Err(SolverError::Backend(
                    "prove: refutation of the negated goal failed its own check".to_owned(),
                ));
            }
            Ok(ProofOutcome::Proved(Box::new(report)))
        }
    }
}

/// Which certified-evidence producer a query should route to.
enum EvidenceRoute {
    /// Only bit-vectors and Booleans — the `produce_qf_bv_evidence` (DRAT) path.
    QfBv,
    /// Only reals and Booleans — the lazy-SMT / Farkas refutation path.
    PureReal,
    /// Anything else supported — the `solve` fallback (replay-certified `sat`).
    Other,
}

/// Classifies a query by the sorts/operators it uses (one traversal), at the
/// granularity the evidence router needs to pick the strongest certificate path.
fn evidence_route(arena: &TermArena, assertions: &[TermId]) -> EvidenceRoute {
    let (mut has_real, mut has_bitvec) = (false, false);
    let (mut has_array, mut has_int) = (false, false);
    let (mut has_func, mut has_quantifier) = (false, false);
    let mut seen = BTreeSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.sort_of(term) {
            Sort::Real => has_real = true,
            Sort::BitVec(_) | Sort::Float { .. } => has_bitvec = true,
            Sort::Array { .. } => has_array = true,
            Sort::Int => has_int = true,
            Sort::Bool | Sort::Datatype(_) => {}
        }
        if let TermNode::App { op, args } = arena.node(term) {
            match op {
                Op::Apply(_) => has_func = true,
                Op::Forall(_) | Op::Exists(_) => has_quantifier = true,
                _ => {}
            }
            stack.extend(args.iter().copied());
        }
    }

    let extra = has_array || has_int || has_func || has_quantifier;
    if !has_real && !extra {
        EvidenceRoute::QfBv // only bit-vectors and Booleans
    } else if has_real && !has_bitvec && !extra {
        EvidenceRoute::PureReal // only reals and Booleans
    } else {
        EvidenceRoute::Other
    }
}
