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
//! - larger `QF_BV` `unsat` in the Alethe driver's fragment carries a complete
//!   Alethe bitblast→CNF→resolution proof; `check` re-runs the independent
//!   [`axeyum_cnf::check_alethe`] kernel, which re-derives the bit-blast itself
//!   (no trusted reduction). This is the stronger upgrade over plain DRAT.
//! - other larger `QF_BV` `unsat` carries an optional [`UnsatProof`] (DIMACS +
//!   DRAT); `check` re-parses and re-runs the trusted [`axeyum_cnf::check_drat`]
//!   kernel. A `None` proof means the result came from the (lower-assurance)
//!   adapter without a DRAT certificate, and is documented as such.
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

use axeyum_cnf::{AletheCommand, check_alethe, check_drat, parse_dimacs, parse_drat};
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
    /// Unsatisfiable (`QF_BV`), certified by a complete Alethe bitblast→CNF→
    /// resolution proof whose [`check_alethe`] re-validation is the evidence —
    /// the bit-blast *reduction itself* is checked (every `bitblast_*` step), not
    /// trusted; also externally checkable by Carcara. This is the upgrade over a
    /// plain DRAT [`Evidence::Unsat`] for the large-instance fragment the Alethe
    /// driver covers: the same `unsat` now carries a proof in which bit-blast,
    /// Tseitin, and the SAT refutation are all re-derived, closing the bit-blast
    /// trust hole.
    UnsatAletheProof(Vec<AletheCommand>),
    /// Unsatisfiable (`QF_LIA`/`QF_LRA` via an Alethe `lia_generic`/`la_generic`
    /// refutation), certified by an **arithmetic-aware** Alethe proof whose
    /// re-validation is the evidence. Unlike [`Evidence::UnsatAletheProof`] (the
    /// bit-blast fragment, checked by the plain [`check_alethe`] kernel), this
    /// proof's `lia_generic`/`la_generic` arithmetic clauses require the
    /// arithmetic checker callback, so `check` runs
    /// [`crate::check_alethe_lra`] (= [`axeyum_cnf::check_alethe_with`] + the
    /// integer/linear Farkas re-derivation). Emitted only when that checker
    /// already accepts the proof (the emitters are self-validating), and the
    /// Farkas/`lia_generic` reduction is **certified** (re-derived), not trusted.
    UnsatArithAletheProof(Vec<AletheCommand>),
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
            Evidence::UnsatAletheProof(proof) => check_alethe(proof).map_err(|e| {
                SolverError::Backend(format!("unsat Alethe evidence re-check failed: {e}"))
            }),
            // Arithmetic Alethe proof: the `lia_generic`/`la_generic` clauses need
            // the arithmetic-aware checker (plain `check_alethe` would reject the
            // arithmetic rule), so re-validate with the integer/linear Farkas
            // callback. A failed re-derivation (or tampered proof) is a clean
            // `Ok(false)`/`Err`, never a silently-accepted bad cert.
            Evidence::UnsatArithAletheProof(proof) => crate::check_alethe_lra(proof).map_err(|e| {
                SolverError::Backend(format!(
                    "unsat arithmetic Alethe evidence re-check failed: {e}"
                ))
            }),
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
                | Evidence::UnsatAletheProof(_)
                | Evidence::UnsatArithAletheProof(_)
                | Evidence::UnsatTermLevel { .. }
                | Evidence::UnsatFarkas(_)
                | Evidence::UnsatLraDpll(_)
        )
    }
}

/// Runs the pure-Rust `QF_BV` pipeline on `assertions` and packages the outcome
/// as a self-checking [`EvidenceReport`]: a `sat` model, or one of the `unsat`
/// certificates in **decreasing assurance precedence**, or `unknown`, each with
/// versioned [`Provenance`]. The `unsat` precedence is:
///
/// 1. **term-level enumeration** (≤20 total symbol bits) — trusts only the
///    evaluator, the strongest;
/// 2. **Alethe bitblast→CNF→resolution proof** ([`Evidence::UnsatAletheProof`])
///    when the instance is in the driver's fragment — `check_alethe` re-derives
///    the bit-blast itself, so all of bit-blast/Tseitin/SAT-refutation are
///    certified this run;
/// 3. **plain DRAT** ([`Evidence::Unsat`]) otherwise — Tseitin + the SAT
///    refutation are DRAT-checked, but the bit-blast is trusted, not certified.
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
    let check = backend.check(arena, assertions, config)?;
    // Did the CDCL(XOR) fallback supply this `unsat` (ADR-0035)? That refutation
    // is the trusted `XorGaussian` hole and is NOT RUP, so it must NOT be routed
    // through term-level enumeration / Alethe / DRAT (which would fail or, for a
    // synthesized proof, be incorrectly rejected). It is recorded as a bare
    // `unsat` carrying the `XorGaussian` (plus bit-blast/Tseitin) trust steps.
    let xor_cdcl_unsat = backend.last_stats().is_some_and(|s| {
        s.backend
            .iter()
            .any(|(name, value)| name == "xor_cdcl_fallback_unsat" && *value > 0.0)
    });
    let (evidence, trusted_steps) = match check {
        CheckResult::Sat(model) => (Evidence::Sat(model), Vec::new()),
        CheckResult::Unknown(reason) => (Evidence::Unknown(reason), Vec::new()),
        CheckResult::Unsat if xor_cdcl_unsat => (
            // Search-only XOR refutation: bit-blast and Tseitin produced the CNF
            // (trusted, not certified on this route), and the XOR Gaussian search
            // refuted it without an RUP-checkable proof — the ledgered hole.
            Evidence::Unsat(None),
            trust_steps(&[
                (TrustId::BitBlast, false),
                (TrustId::Tseitin, false),
                (TrustId::XorGaussian, false),
            ]),
        ),
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
                // Too large to enumerate (or enumeration unsupported). First try
                // the Alethe driver: if the query is in its fragment it yields a
                // complete bitblast→CNF→resolution proof whose `check_alethe`
                // re-validation *certifies* the bit-blast reduction itself (every
                // `bitblast_*` step), upgrading the trust over the plain DRAT route
                // (which trusts the bit-blast). Otherwise fall through to DRAT.
                Ok(CertifyOutcome::DomainTooLarge { .. }) | Err(_) => {
                    if let Some(proof) =
                        crate::qfbv_alethe::prove_qf_bv_unsat_alethe(arena, assertions)
                    {
                        // Defense in depth: re-validate the proof internally before
                        // trusting it as evidence. Only on a clean re-check do we
                        // emit it (with bit-blast/Tseitin/SAT-refutation certified);
                        // any failure falls through to the DRAT export below.
                        if check_alethe(&proof) == Ok(true) {
                            (
                                Evidence::UnsatAletheProof(proof),
                                // The Alethe proof re-derives all three layers, so
                                // each is certified this run (bit-blast included).
                                trust_steps(&[
                                    (TrustId::BitBlast, true),
                                    (TrustId::Tseitin, true),
                                    (TrustId::SatRefutation, true),
                                ]),
                            )
                        } else {
                            drat_qf_bv_evidence(arena, assertions)?
                        }
                    } else {
                        drat_qf_bv_evidence(arena, assertions)?
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

/// The plain DRAT clausal `unsat` evidence for a `QF_BV` query: bit-blast is
/// trusted-not-certified (`false`) on this route, while Tseitin and the SAT
/// refutation are DRAT-checked. Used when the instance is too large to enumerate
/// and the Alethe driver does not cover it (or its re-check fails).
///
/// # Errors
///
/// Returns [`SolverError`] from the proof export, including a soundness alarm if
/// the proof core finds a model where the backend reported `unsat`.
fn drat_qf_bv_evidence(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<(Evidence, Vec<TrustStep>), SolverError> {
    Ok(match export_qf_bv_unsat_proof(arena, assertions)? {
        // Bit-blast is recorded (a miter route exists, but this plain DRAT export
        // does not run it → certified:false); Tseitin + the SAT refutation are
        // DRAT-checked here.
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
                "soundness alarm: backend reported unsat but the proof core found a model"
                    .to_owned(),
            ));
        }
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

/// Runs the **nonlinear** real-arithmetic engine ([`crate::check_with_nra`]) on
/// `assertions` and packages an [`EvidenceReport`]. NRA is sound but incomplete
/// (ADR-0024): a `sat` model is replay-checkable; an `unsat` is recorded as a
/// *bare* `Evidence::Unsat(None)` (a documented trust gap — no transferable
/// certificate yet); `unknown` is the NRA frontier. This is the fallback the
/// front door takes when the linear-real route rejects a nonlinear product.
///
/// # Errors
///
/// Returns [`SolverError`] from the NRA engine.
pub fn produce_nra_evidence(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<EvidenceReport, SolverError> {
    let provenance = Provenance {
        semantics_version: SEMANTICS_VERSION,
        layers: LayerVersions::CURRENT,
        backend: "nra-linear-abstraction".to_owned(),
        assertion_count: assertions.len(),
        timeout: config.timeout,
        resource_limit: config.resource_limit,
        node_budget: config.node_budget,
        cnf_variable_budget: config.cnf_variable_budget,
        cnf_clause_budget: config.cnf_clause_budget,
        prove_unsat: true,
    };
    let evidence = match crate::nra::check_with_nra(arena, assertions, config)? {
        CheckResult::Sat(model) => Evidence::Sat(model),
        CheckResult::Unsat => Evidence::Unsat(None),
        CheckResult::Unknown(reason) => Evidence::Unknown(reason),
    };
    Ok(EvidenceReport {
        evidence,
        provenance,
        trusted_steps: Vec::new(),
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
        // Pure real arithmetic: the lazy-SMT / Farkas linear route first; if it
        // rejects a *nonlinear* product, fall back to the NRA engine (#14: the
        // front door now dispatches nonlinear real goals to NRA instead of
        // hard-erroring `Unsupported`).
        EvidenceRoute::PureReal => {
            return match produce_lra_dpll_evidence(arena, assertions, config) {
                Err(SolverError::Unsupported(msg)) if msg.contains("nonlinear") => {
                    produce_nra_evidence(arena, assertions, config)
                }
                other => other,
            };
        }
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
            // Prefer a check_alethe-validated, ZERO-TRUST-HOLE Alethe refutation when
            // the problem is in a fragment a certifying emitter covers: the array
            // read-over-write-same / extensionality DIRECT cert, the Ackermann
            // (QF_UFBV) functional-consistency cert, or the array-elimination (QF_ABV)
            // read-consistency cert. Each derives the otherwise-*trusted* reduction
            // (functional/read consistency) by `eq_congruent`, so the proof carries no
            // reduction trust hole (re-validated by check_alethe in Evidence::check).
            // Otherwise fall back to the DRAT reduction certificate (which records the
            // trusted reduction steps it went through).
            if let Some(proof) = zero_trust_alethe_certificate(arena, assertions) {
                (Evidence::UnsatAletheProof(proof), Vec::new())
            } else if let Some(proof) = arith_alethe_certificate(arena, assertions) {
                // A pure linear-integer (or otherwise-LRA) `unsat` that reached the
                // `Other` route (e.g. QF_LIA, which `evidence_route` sends here):
                // the `lia_generic`/`la_generic` Alethe proof is re-checked by the
                // arithmetic-aware checker, so the Farkas reduction is CERTIFIED.
                // Ordered AFTER `zero_trust_alethe_certificate` (so UF/array/
                // datatype keep their zero-trust cert); the LIA/LRA emitters return
                // `None` for those fragments, so this never shadows them.
                (
                    Evidence::UnsatArithAletheProof(proof),
                    trust_steps(&[(TrustId::Farkas, true)]),
                )
            } else {
                let (cert, steps) = reduction_unsat_certificate(arena, assertions);
                (Evidence::Unsat(cert), steps)
            }
        }
        CheckResult::Unknown(reason) => (Evidence::Unknown(reason), Vec::new()),
    };
    Ok(EvidenceReport {
        evidence,
        provenance,
        trusted_steps,
    })
}

/// Tries each **zero-trust-hole** Alethe certificate emitter in turn, returning the
/// first that produces a [`check_alethe`]-validated refutation closing to `(cl)`:
///
/// 1. [`crate::prove_qf_abv_unsat_alethe`] — the array read-over-write-same /
///    extensionality DIRECT cert (proves the conflict via the array axiom);
/// 2. [`crate::prove_qf_ufbv_unsat_alethe`] — the Ackermann (`QF_UFBV`) cert (derives
///    each functional-consistency constraint by `eq_congruent`);
/// 3. [`crate::prove_qf_abv_unsat_alethe_via_elimination`] — the array-elimination
///    (`QF_ABV`) cert (derives each read-consistency constraint by `eq_congruent`);
/// 4. [`crate::prove_qf_dt_unsat_alethe_via_simplification`] — the datatype
///    read-over-construct cert (folds each `select`-over-`construct` by
///    `eq_transitive`, the projection discharged by ι-reduction — no datatype axiom).
///
/// Each emitter is self-validating (returns `Some` only after `check_alethe`
/// accepts), and outside its fragment returns `None` cheaply — so trying them in
/// order is sound and a returned proof is genuinely checkable with **no trusted
/// reduction step**: its `eq_congruent` derivations replace the previously-trusted
/// Ackermann / array-elimination reductions. The defensive `check_alethe` re-gate
/// mirrors the historical call site (a belt-and-braces re-validation).
fn zero_trust_alethe_certificate(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    if let Some(proof) = crate::prove_qf_abv_unsat_alethe(arena, assertions)
        && matches!(check_alethe(&proof), Ok(true))
    {
        return Some(proof);
    }
    if let Some(proof) = crate::prove_qf_ufbv_unsat_alethe(arena, assertions)
        && matches!(check_alethe(&proof), Ok(true))
    {
        return Some(proof);
    }
    if let Some(proof) = crate::prove_qf_abv_unsat_alethe_via_elimination(arena, assertions)
        && matches!(check_alethe(&proof), Ok(true))
    {
        return Some(proof);
    }
    if let Some(proof) = crate::prove_qf_dt_unsat_alethe_via_simplification(arena, assertions)
        && matches!(check_alethe(&proof), Ok(true))
    {
        return Some(proof);
    }
    None
}

/// Tries the **arithmetic** Alethe certificate emitters in turn, returning the
/// first that produces a [`crate::check_alethe_lra`]-validated refutation:
///
/// 1. [`crate::prove_lia_unsat_alethe`] — the linear-integer (`QF_LIA`)
///    `lia_generic` cert (e.g. `x >= 1 ∧ x <= -1`);
/// 2. [`crate::prove_lra_unsat_alethe`] — the linear-real (`QF_LRA`) `la_generic`
///    cert, for any conjunctive LRA `unsat` that reaches the `Other` route.
///
/// Each emitter is self-validating (returns `Some` only after `check_alethe_lra`
/// accepts) and returns `None` cheaply outside its fragment — in particular for
/// UF / array / datatype / quantifier queries — so trying them after
/// [`zero_trust_alethe_certificate`] never shadows those zero-trust certs, and a
/// returned proof is genuinely re-checkable by the arithmetic-aware checker.
/// The defensive `check_alethe_lra` re-gate mirrors the historical call sites.
fn arith_alethe_certificate(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    if let Some(proof) = crate::prove_lia_unsat_alethe(arena, assertions)
        && matches!(crate::check_alethe_lra(&proof), Ok(true))
    {
        return Some(proof);
    }
    if let Some(proof) = crate::prove_lra_unsat_alethe(arena, assertions)
        && matches!(crate::check_alethe_lra(&proof), Ok(true))
    {
        return Some(proof);
    }
    None
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
        | Evidence::UnsatAletheProof(_)
        | Evidence::UnsatArithAletheProof(_)
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
    let mut has_datatype = false;
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
            // A datatype-sorted subterm signals a datatype query even when every
            // top-level asserted term is Bool/BitVec (e.g. `select(mk(a,b), 0) =
            // #b00`): it must route to `solve`, not the raw BV bit-blaster.
            Sort::Datatype(_) => has_datatype = true,
            Sort::Bool => {}
        }
        if let TermNode::App { op, args } = arena.node(term) {
            match op {
                Op::Apply(_) => has_func = true,
                Op::Forall(_) | Op::Exists(_) => has_quantifier = true,
                // Constructor/selector/tester ops are datatype features even when
                // their result sort is BitVec/Bool (a `select`/`is-c` over a
                // datatype): route to `solve`, which has the datatype dispatch.
                Op::DtConstruct { .. } | Op::DtSelect { .. } | Op::DtTest(_) => {
                    has_datatype = true;
                }
                _ => {}
            }
            stack.extend(args.iter().copied());
        }
    }

    let extra = has_array || has_int || has_func || has_quantifier || has_datatype;
    if !has_real && !extra {
        EvidenceRoute::QfBv // only bit-vectors and Booleans
    } else if has_real && !has_bitvec && !extra {
        EvidenceRoute::PureReal // only reals and Booleans
    } else {
        EvidenceRoute::Other
    }
}
