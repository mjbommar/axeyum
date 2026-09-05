//! Self-checking evidence envelopes (ADR-0005 follow-through).
//!
//! [`Evidence`] is a result paired with the artifact that justifies it, and a
//! single [`Evidence::check`] that **re-validates it independently** of the
//! solver that produced it — the "trusted small checking" identity made
//! consumer-facing:
//!
//! - `sat` carries a [`Model`]; `check` replays it through the ground evaluator
//!   against the original assertions.
//! - small `QF_BV`/finite Bool/BV `unsat` carries a **term-level** certificate
//!   (the strongest: exhaustive evaluation over the finite symbol/quantifier
//!   domain, trusting only the evaluator — not the bit-blaster, CNF encoder, or
//!   SAT solver); `check` re-enumerates.
//! - larger `QF_BV` `unsat` in the Alethe driver's fragment carries a complete
//!   Alethe bitblast→CNF→resolution proof; `check` re-runs the independent
//!   [`axeyum_cnf::check_alethe`] kernel, which re-derives the bit-blast itself
//!   (no trusted reduction). This is the stronger upgrade over plain DRAT.
//! - other larger `QF_BV` `unsat` carries an optional [`UnsatProof`] (DIMACS +
//!   DRAT, and normally LRAT); `check` re-parses and delegates to
//!   [`UnsatProof::recheck`], whose accepting authority is the trusted
//!   search-free [`axeyum_cnf::check_lrat`] when hints are present and the
//!   trusted forward [`axeyum_cnf::check_drat`] when they are not (ADR-0613).
//!   A `None` proof means the result came from the (lower-assurance)
//!   adapter without a DRAT certificate, and is documented as such — and it
//!   **does not pass the check**, see below.
//! - `QF_LRA` `unsat` carries a [`FarkasCertificate`]; `check` re-runs the
//!   independent [`FarkasCertificate::verify`] (the exact-arithmetic dual of the
//!   DRAT route).
//! - Boolean-structured pure-real `unsat` carries an [`LraDpllRefutation`];
//!   `check` re-runs [`LraDpllRefutation::verify`].
//! - Boolean-structured linear-arithmetic `unsat` carries an
//!   [`ArithDpllRefutation`]; `check` re-runs [`ArithDpllRefutation::verify`].
//! - a **bare `unsat`** ([`Evidence::Unsat(None)`](Evidence::Unsat)) and an
//!   `unknown` carry **nothing to check**.
//!
//! # "Checked" never means "there was nothing to check" (ADR-0384)
//!
//! [`Evidence::check_outcome`] is the three-valued re-validation API:
//! [`EvidenceCheck::Verified`] (a certificate was present and this run
//! re-derived it), [`EvidenceCheck::NothingToCheck`] (no certificate, or no
//! faithful subject to check it against — *not* a pass), and
//! [`EvidenceCheck::Failed`] (a certificate was present and did not hold up).
//! The boolean [`Evidence::check`] is exactly `check_outcome(..) == Verified`,
//! so `if evidence.check(..)? { /* trust it */ }` cannot be satisfied by an
//! uncertified result. Use [`Evidence::is_certified`] to ask the *static*
//! question ("does this variant carry a certificate at all?") without running
//! the checker.
//!
//! [`produce_qf_bv_evidence`], [`produce_lra_evidence`], and
//! [`produce_lra_dpll_evidence`] run the per-theory pipelines, and
//! [`produce_evidence`] is the unified front door that routes any supported query
//! to the producer with the strongest available certificate (mirroring
//! [`crate::solve`]). [`produce_evidence_smtlib_with_script`] is the text front
//! door that hands back the parsed [`axeyum_smtlib::Script`] with the report, so
//! a consumer can re-check its own result without re-parsing.

use std::collections::BTreeSet;
use std::time::{Duration, Instant};

use axeyum_cnf::{AletheCommand, check_alethe};
use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode, TermStats};

use crate::abv::{
    ConstArrayDefaultMismatchCertificate, CrossStoreArrayDisequalityCertificate,
    StoreChainReadbackCertificate,
};
use crate::array_axiom::ArrayAxiomRefutationCertificate;
use crate::array_binary_search::BinarySearch16Certificate;
use crate::array_bv_abs::BvAbstractionRefutationCertificate;
use crate::array_fifo::FifoBc04Certificate;
use crate::array_finite::{BoolArrayReadCollapseCertificate, FiniteArrayExtensionalityCertificate};
use crate::array_memcpy::TwoByteMemcpyRefutationCertificate;
use crate::array_sort2::{TwoElementBubbleSortCertificate, TwoElementSelectionSortCertificate};
use crate::array_write_chain::AlignedWriteChainCommutationCertificate;
use crate::array_xor_swap::{TwoByteXorSwapRoundtripCertificate, TwoCellXorSwapCertificate};
use crate::auto::{BoundedIntBlastCertificate, certify_bounded_int_blast, solve};
use crate::backend::{CheckResult, SolverBackend, SolverConfig, SolverError, UnknownReason};
use crate::bool_euf::{BoolEufExhaustiveCertificate, BoolEufOnlineCertificate};
use crate::bool_simplify::BoolSimplificationRefutationCertificate;
use crate::bv_defined_enum::BvDefinedEnumRefutationCertificate;
use crate::bv_forall_nonconstant::BvForallNonconstantRefutationCertificate;
use crate::bv_uf_local::BvUfLocalRefutationCertificate;
use crate::certify::{
    CertifyOutcome, certify_finite_bv_by_enumeration, certify_qf_bv_by_enumeration,
};
use crate::counterexample::ModelMinimizeOutcome;
use crate::datatype_acyclicity::DatatypeStructuralRefutationCertificate;
use crate::dpll_lia::{ArithDpllOutcome, ArithDpllRefutation, certify_arith_dpll_unsat};
use crate::dpll_t::{LraDpllOutcome, LraDpllRefutation, certify_lra_dpll_unsat};
use crate::lia_gcd::{
    DiophantineCertificate, Equality, check_diophantine_certificate,
    prove_lia_unsat_by_diophantine_certified,
};
use crate::lra::{FarkasCertificate, lra_farkas_certificate};
use crate::model::Model;
use crate::nia_square::IntQuadraticNegativeDiscriminantCertificate;
use crate::nia_univariate_cert::IntUnivariateRefutationCertificate;
use crate::nra_even_power::NraEvenPowerRefutationCertificate;
use crate::nra_handelman_cert::HandelmanRefutationCertificate;
use crate::nra_monomial_bound_cert::MonomialBoundRefutationCertificate;
use crate::nra_product_cert::RealProductRefutationCertificate;
use crate::nra_real_root::{self, SosCertificate};
use crate::nra_zero_product_cert::RealZeroProductRefutationCertificate;
use crate::proof::{
    CheckBudget, CheckingProgress, UnsatProof, UnsatProofOutcome,
    export_qf_bv_unsat_proof_with_progress, export_qf_bv_unsat_proof_within_with_check_budget,
};
use crate::quant_affine_growth_cert::IntAffineGrowthRefutationCertificate;
use crate::quant_bv_alternation_cert::BvAlternationCounterexampleCertificate;
use crate::quant_bv_conjunctive_cert::BvConjunctiveUniversalInstanceCertificate;
use crate::quant_bv_instance_set_cert::BvPositiveUniversalInstanceSetCertificate;
use crate::quant_bv_paired_exists_cert::BvPairedExistentialTransferCertificate;
use crate::quant_closed_counterexample_cert::ClosedUniversalCounterexampleCertificate;
use crate::quant_counterexample_cover::QuantifiedCounterexampleCoverCertificate;
use crate::quant_eq_partition_cert::EqualityPartitionRefutationCertificate;
use crate::quant_finite_cert::{
    GuardedUniversalForm, check_alethe_lra_guarded_inst_against, guarded_universal_form,
    guarded_universal_form_uf, prove_finite_int_quant_unsat_alethe,
    prove_finite_int_quant_unsat_uf_alethe,
};
use crate::quant_negated_exists_cert::NegatedExistentialWitnessCertificate;
use crate::quant_nested_xor_cert::IntNestedXorRefutationCertificate;
use crate::quant_residue_cert::IntEuclideanResidueRefutationCertificate;
use crate::quant_vacuous_exists_counterexample_cert::VacuousExistsUniversalCounterexampleCertificate;
use crate::sat_bv_backend::SatBvBackend;
use crate::set_cardinality::SetCardinalityRefutationCertificate;
use crate::string_length_cert::StringLengthRefutationCertificate;
use crate::term_identity::TermIdentityRefutationCertificate;
use crate::trust::{TrustId, TrustStep};
use crate::uf_arith::UfArithCongruenceCertificate;
use crate::ufbv_finite::{BoolUfExhaustiveCertificate, FiniteDomainPigeonholeCertificate};

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
    /// SAT engine identity/behaviour version. ADR-1703 made the in-tree native
    /// CDCL core the engine on every path, so this reads `axeyum-native-cdcl`
    /// where it used to read `rustsat-batsat`.
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
        sat_adapter: "axeyum-native-cdcl",
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

/// Whether an [`Evidence`] is an `unsat`-family certificate (anything but a `sat`
/// model or an `unknown`) — i.e. a result whose reductions the trust ledger
/// records. Used to gate attaching the `Fpa2Bv` trust step (task #69): `sat` is
/// replay-checked and `unknown` records no reductions.
fn is_unsat_evidence(evidence: &Evidence) -> bool {
    !matches!(evidence, Evidence::Sat(_) | Evidence::Unknown(_))
}

/// Returns `existing` trust steps with a [`TrustId::Fpa2Bv`] step appended at its
/// canonical position (task #69). Re-running [`trust_steps`] keeps the
/// deterministic [`crate::trust::ALL_TRUST_IDS`] order. `certified` is the parser's
/// [`FpUsage::fpa2bv_simple_op_certified`](axeyum_smtlib::FpUsage::fpa2bv_simple_op_certified)
/// verdict — `true` only when every FP operator the reduction lowered is
/// structurally exact, never otherwise.
fn with_fpa2bv_step(existing: &[TrustStep], certified: bool) -> Vec<TrustStep> {
    let mut pairs: Vec<(TrustId, bool)> = existing.iter().map(|s| (s.id, s.certified)).collect();
    pairs.push((TrustId::Fpa2Bv, certified));
    trust_steps(&pairs)
}

/// Why an [`Evidence`] had **nothing** for [`Evidence::check_outcome`] to
/// re-validate (ADR-0384). A `NothingToCheck` is never a pass: it is the honest
/// report that this run verified *nothing*.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NoCheckReason {
    /// A bare [`Evidence::Unsat(None)`](Evidence::Unsat): the verdict is the
    /// deciding engine's, with no transferable certificate attached. Sound if
    /// the engine is, but nothing here was re-derived.
    UncertifiedUnsat,
    /// [`Evidence::Unknown`]: no verdict was claimed, so there is no claim to
    /// re-validate.
    Undecided,
    /// A `sat` model offered against an **empty** assertion list. Replaying a
    /// model over zero assertions succeeds vacuously, so it is reported as
    /// nothing-checked rather than as a verification.
    EmptySubject,
    /// The `(arena, assertions)` subject is not a faithful view of the query the
    /// evidence decided — the bounded/empty flat view of a string script (see
    /// [`produce_evidence_smtlib_with_script`] and ADR-0061). Checking against
    /// it would be meaningless in exactly the direction that fabricates a pass.
    UnfaithfulSubject,
}

impl NoCheckReason {
    /// Stable short label for artifact metadata and diagnostics.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            NoCheckReason::UncertifiedUnsat => "uncertified-unsat",
            NoCheckReason::Undecided => "undecided",
            NoCheckReason::EmptySubject => "empty-subject",
            NoCheckReason::UnfaithfulSubject => "unfaithful-subject",
        }
    }
}

/// The outcome of independently re-validating an [`Evidence`] (ADR-0384).
///
/// Three-valued on purpose: a boolean cannot distinguish "I re-derived the
/// certificate" from "there was no certificate", and conflating them is a green
/// gate over an empty set.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvidenceCheck {
    /// A certificate was present and **this run independently re-derived it**.
    /// The only value that licenses trusting the result on the evidence alone.
    Verified,
    /// Nothing was re-validated, for the carried reason. Not a pass.
    NothingToCheck(NoCheckReason),
    /// A certificate was present and **failed** re-validation. A soundness
    /// alarm: the producer and the checker disagree.
    Failed,
}

impl EvidenceCheck {
    /// Whether an independent certificate was re-derived this run.
    #[must_use]
    pub const fn is_verified(self) -> bool {
        matches!(self, EvidenceCheck::Verified)
    }

    /// Whether the checker had nothing to re-validate.
    #[must_use]
    pub const fn is_nothing_to_check(self) -> bool {
        matches!(self, EvidenceCheck::NothingToCheck(_))
    }

    /// Whether a present certificate failed re-validation (a soundness alarm).
    #[must_use]
    pub const fn is_failed(self) -> bool {
        matches!(self, EvidenceCheck::Failed)
    }

    /// Stable short label for artifact metadata and diagnostics.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            EvidenceCheck::Verified => "verified",
            EvidenceCheck::NothingToCheck(_) => "nothing-to-check",
            EvidenceCheck::Failed => "failed",
        }
    }
}

/// A decided (or undecided) result together with its checkable justification.
#[derive(Debug, Clone)]
pub enum Evidence {
    /// Satisfiable: a model whose canonical replay against the query is the
    /// evidence. Infinite-domain quantified models may carry checked Skolem
    /// certificates consumed by [`crate::check_model`].
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
    /// Unsatisfiable (a **finite-expansion guarded-`Int` universal**), certified by
    /// an Alethe refutation whose instantiation steps are the `forall_inst_guarded`
    /// rule (the finite-`Int` instantiation lemma `∀x.(g⇒i) ∧ g[v] ⊢ i[v]` at each
    /// in-range `v`) and whose ground tail is a `lia_generic` refutation. `check`
    /// re-runs [`crate::check_alethe_lra_guarded_inst_against`] with the carried
    /// [`GuardedUniversalForm`] and the original assertions, which re-derives **both**
    /// halves of each instantiation step — the structural substitution and the
    /// concrete guard truth — so the quantifier-instantiation reduction is *certified,
    /// not trusted*. It additionally verifies that **every `assume` is a sound premise
    /// of the original query** (the universal, an original assertion, a genuinely-fresh
    /// Ackermann definition, or the abstracted form of an original side fact), so the
    /// certificate is **assume-independent**: no premise is trusted from the emitter.
    /// This is the first quantified-`unsat` evidence variant: it upgrades the
    /// otherwise-bare `Evidence::Unsat(None)` for the guarded-finite-`Int` fragment to
    /// an independently re-checkable certificate.
    UnsatGuardedQuantAletheProof {
        /// The `forall_inst_guarded` + `lia_generic` refutation closing to `(cl)`.
        proof: Vec<AletheCommand>,
        /// The guarded universal's form the `forall_inst_guarded` hook re-checks
        /// each instantiation step against (binder name, guarded body, inner
        /// consequent, and the `[lo, hi]` range).
        universal: GuardedUniversalForm,
    },
    /// Unsatisfiable (quantified `LIA`), certified by independently re-matching
    /// the exact Euclidean quotient/remainder partition
    /// `forall s m. k*m+s != t or s<0 or s>=k`, with constant `k>0` and a
    /// dividend independent of both binders. The checker derives the concrete
    /// counterexample `s=mod(t,k), m=div(t,k)` directly from SMT-LIB integer
    /// division/modulo semantics; no result from the instantiation search is
    /// trusted.
    UnsatIntEuclideanResidue(IntEuclideanResidueRefutationCertificate),
    /// Unsatisfiable (quantified `LIA`), certified by independently re-matching
    /// the exact positive-slope piecewise universal from ADR-0097. Two
    /// consecutive Euclidean-division counterexamples ensure that one selects
    /// the unbounded else branch; no search-generated instance is trusted.
    UnsatIntAffineGrowth(IntAffineGrowthRefutationCertificate),
    /// Unsatisfiable (quantified `LIA`), certified by independently re-matching
    /// the exact nested-XOR selector theorem from ADR-0099. The checker proves
    /// that two outer pivot instances expose a nested universal whose off-pivot
    /// instance equates distinct integer constants.
    UnsatIntNestedXor(IntNestedXorRefutationCertificate),
    /// Unsatisfiable because one original top-level closed universal has a
    /// concrete scalar assignment that makes its quantifier-free body false.
    /// The checker evaluates that untouched body under the carried original
    /// binder values; search substitutions and the QF solver are not replayed.
    UnsatClosedUniversalCounterexample(ClosedUniversalCounterexampleCertificate),
    /// Unsatisfiable because a leading nonempty existential block is
    /// syntactically vacuous and one complete assignment falsifies the closed
    /// Bool/BV universal body beneath it. The checker revalidates vacuity and
    /// evaluates the untouched body under the carried universal values.
    UnsatVacuousExistsUniversalCounterexample(VacuousExistsUniversalCounterexampleCertificate),
    /// Unsatisfiable because one original top-level negated existential has a
    /// concrete complete Bool/BV witness that makes its untouched body true.
    UnsatNegatedExistentialWitness(NegatedExistentialWitnessCertificate),
    /// Unsatisfiable because one concrete assignment to a closed Bool/BV
    /// universal block makes the following existential matrix QF_BV-UNSAT.
    /// Replay regenerates the exact residual source formula and checks its DRAT.
    UnsatBvAlternationCounterexample(BvAlternationCounterexampleCertificate),
    /// Unsatisfiable because replacing one positive universal conjunct by a
    /// complete concrete source instance yields checked QF_BV-UNSAT.
    UnsatBvConjunctiveUniversalInstance(BvConjunctiveUniversalInstanceCertificate),
    /// Unsatisfiable because a query-scoped set of complete concrete instances
    /// of admitted positive Bool/BV universals makes the rebuilt ground query
    /// QF_BV-UNSAT. Replay regenerates every instance and checks its DRAT/LRAT.
    UnsatBvPositiveUniversalInstanceSet(BvPositiveUniversalInstanceSetCertificate),
    /// Unsatisfiable because a positive existential assertion and the negation
    /// of a second existential assertion have identical ground premises, and
    /// the first body transfers its complete witness tuple to the second.
    /// Replay alpha-aligns both source prefixes and checks every transferred
    /// conjunct structurally or by a source-bound `QF_BV` proof.
    UnsatBvPairedExistentialTransfer(BvPairedExistentialTransferCertificate),
    /// Unsatisfiable because a closed Bool/Int quantified assertion is false
    /// over the exact finite quotient induced by binder-to-constant equality
    /// predicates. The checker recursively evaluates the untouched formula.
    UnsatEqualityPartition(EqualityPartitionRefutationCertificate),
    /// Unsatisfiable because finitely many source-instantiated Bool/Int
    /// counterexamples exclude a cover of every free-Boolean ground model. The
    /// checker re-proves each sufficient cube against its exact universal
    /// instance and re-proves closure of the weakened ground skeleton.
    UnsatQuantifiedCounterexampleCover(QuantifiedCounterexampleCoverCertificate),
    /// Unsatisfiable by **e-matching**: universals instantiated at ground terms
    /// until the quantifier-free set is refuted. The checker replays every
    /// instance against the untouched assertions with the driver's own public
    /// checker, rejects a ground member that is neither asserted nor derived,
    /// and **re-refutes the ground set** — provenance alone would certify a pile
    /// of true-but-insufficient instances.
    ///
    /// This is the route that previously reported `unsat-uncertified` for every
    /// query it decided, despite recording exactly the provenance needed.
    UnsatQuantInstanceSet(crate::quant_instance_set_cert::QuantifierInstanceSetCertificate),
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
    /// Unsatisfiable (finite Bool/BV, including finite quantifiers), certified by
    /// exhaustive evaluation over all free Bool/BV symbol assignments while the
    /// evaluator itself enumerates bound Bool/BV quantifier domains. This is the
    /// quantified counterpart of [`Evidence::UnsatTermLevel`].
    UnsatFiniteDomainEnum {
        /// Number of finite cases covered by the certificate budget.
        cases: u64,
        /// The combined free-symbol plus bound-quantifier bit budget used.
        max_total_bits: u32,
    },
    /// Unsatisfiable (`BV`/Bool): exhaustive enumeration after applying checked
    /// top-level symbol definitions and finite-domain restrictions. This covers
    /// finite-field rows where raw symbol enumeration is too wide, but required
    /// equalities define helper symbols and bit/range constraints shrink the
    /// remaining independent domains. The checker re-scans the original query,
    /// recomputes the definitions/domains, and replays every covered assignment.
    UnsatBvDefinedEnum(BvDefinedEnumRefutationCertificate),
    /// Unsatisfiable (quantified `BV`): a universal equality forces a visibly
    /// non-constant BV expression to be one fixed result for every quantified
    /// value. The checker re-scans the original query and re-matches the exact
    /// witness schema before accepting.
    UnsatBvForallNonconstant(BvForallNonconstantRefutationCertificate),
    /// Unsatisfiable (`BV` + UF): tiny local pure-BV enumeration derives
    /// equality facts, then congruence closure over the original UF terms closes
    /// a disequality or a one-step pure-BV contradiction. The checker re-scans
    /// the original query and recomputes the certificate before accepting.
    UnsatBvUfLocal(BvUfLocalRefutationCertificate),
    /// Unsatisfiable: lowered finite-set cardinality constraints refute by
    /// popcount monotonicity, subset facts, and safe union/intersection upper
    /// bounds. The checker re-scans the original lowered BV assertions and
    /// re-matches the conflicting bounds before accepting.
    UnsatSetCardinality(SetCardinalityRefutationCertificate),
    /// Unsatisfiable (`QF_LRA`): a Farkas refutation over the exact-rational
    /// constraints, whose [`FarkasCertificate::verify`] is the evidence.
    UnsatFarkas(FarkasCertificate),
    /// Unsatisfiable (Boolean-structured pure-real `QF_LRA`): a lazy-SMT
    /// refutation (skeleton + Farkas-certified theory lemmas) whose
    /// [`LraDpllRefutation::verify`] is the evidence.
    UnsatLraDpll(LraDpllRefutation),
    /// Unsatisfiable (Boolean-structured `QF_LIA`/`QF_LRA`): a lazy-SMT
    /// refutation (Boolean skeleton plus exact-theory checked lemmas) whose
    /// [`ArithDpllRefutation::verify`] is the evidence.
    UnsatArithDpll(ArithDpllRefutation),
    /// Unsatisfiable (`NRA`): a self-checking degree-2 sum-of-squares / PSD
    /// refutation of a STRICT quadratic inequality atom. The `certificate`'s
    /// [`SosCertificate::verify`] (an exact-rational `LDLᵀ` reconstruction, fully
    /// independent of the producer) is the primary evidence (ADR-0039); when
    /// `lean_module` is present, the refutation is ALSO backed by a kernel-checked
    /// Lean proof, re-derived and re-checked on `Evidence::check` (ADR-0041).
    UnsatSos {
        /// The exact-rational SOS/PSD certificate (self-checked by `verify`).
        certificate: SosCertificate,
        /// The rendered Lean module, when SOS→Lean reconstruction succeeded for the
        /// query. `check` re-runs the reconstruction (the kernel re-verifies it); the
        /// stored string is for output, not trusted on its own.
        lean_module: Option<String>,
    },
    /// Unsatisfiable (`QF_NIA`): one source integer quadratic equality has a
    /// negative discriminant, so it has no real and therefore no integer root.
    /// Replay re-collects the exact original assertion and recomputes the
    /// discriminant; no producer-local term identity is trusted.
    UnsatIntQuadraticNegativeDiscriminant(IntQuadraticNegativeDiscriminantCertificate),
    /// Unsatisfiable (`QF_NIA`): a single-variable integer polynomial
    /// **equality** refuted by one of three exact arguments — a non-square
    /// discriminant, rational-but-non-integral quadratic roots, or exhaustion of
    /// the rational-root candidates for degree ≥ 3. `nia_square` decided these
    /// exactly all along; nothing emitted the reasoning, so they shipped as bare
    /// `Evidence::Unsat(None)` and `QF_NIA` sat in *band 2 — model replay only*.
    ///
    /// The checker re-collects the polynomial from the untouched assertion and
    /// then re-derives the refutation **from the coefficients alone**, using an
    /// argument that shares no code with the producer — so unlike a
    /// `fresh == cert` re-execution it can disagree with the producer rather
    /// than only with a different query.
    UnsatIntUnivariatePoly(IntUnivariateRefutationCertificate),
    /// Unsatisfiable (`NRA`): the query asserts a syntactic sum of even powers
    /// plus a nonnegative rational constant is strictly negative. The checker
    /// re-scans the original assertions and re-matches the exact nonnegativity
    /// shape before accepting.
    UnsatNraEvenPower(NraEvenPowerRefutationCertificate),
    /// Unsatisfiable (`QF_NRA`): a monomial asserted zero divides a monomial
    /// asserted non-zero, so the second is zero too. Also covers the case-split
    /// form, where a disjunction zeroes one variable per arm and **every** arm's
    /// variable is a factor of the non-zero monomial.
    ///
    /// Factors are carried by SOURCE NAME, not `SymbolId`: ids are arena-local
    /// and mean nothing against a fresh parse, which is what re-validation uses.
    UnsatRealZeroProduct(RealZeroProductRefutationCertificate),
    /// Unsatisfiable (`QF_NRA`): the product of two asserted lower-bound
    /// hypotheses is exactly the polynomial a third assertion claims negative.
    /// A degree-2 Positivstellensatz refutation, checkable with exact rational
    /// arithmetic and no CAD.
    ///
    /// Strictness is carried, not assumed: `p ≥ 0` and `q ≥ 0` give `pq ≥ 0`,
    /// which refutes `pq < 0` but NOT `pq ≤ 0`. Only two strict factors refute
    /// both.
    UnsatRealProduct(RealProductRefutationCertificate),
    /// Unsatisfiable (`QF_NRA`): a multi-term Handelman / Positivstellensatz
    /// combination. Products of asserted hypotheses, with positive rational
    /// coefficients, plus polynomial multiples of asserted equalities, summing to
    /// a constant that a sum of nonnegative terms cannot equal. One combination
    /// per case when the refutation splits a top-level disjunction.
    ///
    /// Strictness decides whether a residual of exactly zero closes: a sum of
    /// nonnegative products is `>= 0`, which contradicts `= 0` only when one term
    /// is strictly positive. Every atom's strictness is carried and re-derived.
    UnsatRealHandelman(HandelmanRefutationCertificate),
    /// Unsatisfiable (`QF_NRA`): per-variable bounds multiply into a bound on a
    /// monomial that contradicts an asserted atom — either `M >= lo` against
    /// `M < lo`, or every factor pinned so `M == k` against `M != k`.
    ///
    /// An EVEN exponent needs no bound (`x^2 >= 0` for every real `x`); an odd
    /// one on an unbounded variable leaves the monomial unbounded below, so the
    /// parity is carried and re-checked rather than assumed.
    UnsatMonomialBound(MonomialBoundRefutationCertificate),
    /// Unsatisfiable (integer-equality systems): a self-checking "integer Farkas" /
    /// Diophantine refutation of an integer-infeasible system of equalities. The
    /// `certificate`'s independent re-checker [`check_diophantine_certificate`]
    /// (re-derives `Σ λᵢ·Eᵢ` and confirms `gcd ∤ constant`, fully independent of the
    /// producer) is the primary evidence (ADR-0042); when `lean_module` is present,
    /// the refutation is ALSO backed by a kernel-checked Lean proof, re-derived and
    /// re-checked on `Evidence::check` (ADR-0043).
    UnsatDiophantine {
        /// The original normalized integer equalities the certificate refers to.
        equalities: Vec<Equality>,
        /// The integer-Farkas certificate (self-checked by
        /// [`check_diophantine_certificate`]).
        certificate: DiophantineCertificate,
        /// The rendered Lean module, when Diophantine→Lean reconstruction succeeded
        /// for the query. `check` re-runs the reconstruction (the kernel re-verifies
        /// it); the stored string is for output, not trusted on its own.
        lean_module: Option<String>,
    },
    /// Unsatisfiable (`QF_NIA`/bounded integer arithmetic): a proven finite integer
    /// box plus an exactly-encoded bounded-int blast whose regenerated DIMACS is
    /// DRAT-refuted. The checker re-derives the box and covering width from the
    /// original assertions, regenerates the clamped DIMACS, and rechecks DRAT.
    UnsatBoundedIntBlast(BoundedIntBlastCertificate),
    /// Unsatisfiable (`QF_UFBV`): a finite-domain pigeonhole refutation. The
    /// checker re-scans the original top-level conjunction and confirms it
    /// requires more pairwise-distinct applications of one function than that
    /// function's finite Bool/BV argument tuple domain can provide.
    UnsatFiniteDomainPigeonhole(FiniteDomainPigeonholeCertificate),
    /// Unsatisfiable (`QF_UFBV`/`QF_UF` over Booleans): a tiny exhaustive
    /// finite-Boolean-UF refutation. The checker re-enumerates every assignment
    /// to the reachable Boolean symbols and every truth table for reachable
    /// `Bool^n -> Bool` functions, accepting only when every case falsifies an
    /// original assertion.
    UnsatBoolUfExhaustive(BoolUfExhaustiveCertificate),
    /// Unsatisfiable (`QF_UF`): a bounded Boolean-structured EUF refutation. The
    /// checker enumerates satisfying Boolean assignments to equality atoms and
    /// re-runs congruence closure on each induced equality/disequality core.
    UnsatBoolEufExhaustive(BoolEufExhaustiveCertificate),
    /// Unsatisfiable (`QF_UF`): a larger Boolean-structured EUF refutation. The
    /// checker re-runs the deterministic online EUF DPLL(T) refuter over the
    /// original assertions and accepts only if it returns `unsat`.
    UnsatBoolEufOnline(BoolEufOnlineCertificate),
    /// Unsatisfiable (`QF_UFLIA`): congruence over mixed uninterpreted sorts
    /// derives arithmetic equalities, then checked arithmetic DPLL refutes the
    /// retained Boolean-structured linear-arithmetic residual.
    UnsatUfArithCongruence(UfArithCongruenceCertificate),
    /// Unsatisfiable (`QF_DT`): datatype structural axioms
    /// (acyclicity/distinctness/injectivity/exhaustiveness) refute either the top-level
    /// conjunction directly or every branch of a top-level datatype disjunction.
    /// The checker re-scans the original query and re-matches the structural
    /// refutation before accepting.
    UnsatDatatypeStructural(DatatypeStructuralRefutationCertificate),
    /// Unsatisfiable (`QF_ABV`/`QF_AUFBV`): a finite-array extensionality
    /// refutation. The checker re-scans the original top-level conjunction and
    /// confirms it asserts two arrays over a small finite BV index domain are
    /// unequal while also asserting their reads equal at every concrete index.
    UnsatFiniteArrayExtensionality(FiniteArrayExtensionalityCertificate),
    /// Unsatisfiable (`QF_AX`): one Bool-index array has equal `false` and
    /// `true` reads, contradicting an asserted disequality between two reads of
    /// that same array. The checker re-scans the original assertions and
    /// re-matches the exact certificate.
    UnsatBoolArrayReadCollapse(BoolArrayReadCollapseCertificate),
    /// Unsatisfiable (`QF_ABV`/`QF_AUFBV`): the query asserts the negation of one
    /// of a small set of checked array axiom schemas (read-over-write,
    /// select-over-ite, or store-over-ite under select). The checker re-scans the
    /// original assertions and re-matches the exact schema before accepting.
    UnsatArrayAxiom(ArrayAxiomRefutationCertificate),
    /// Unsatisfiable (`QF_ALIA`): finite write chains over two different
    /// constant-array defaults on the infinite `Int` index sort. The checker
    /// re-scans the original assertions and re-matches the exact certificate.
    UnsatConstArrayDefaultMismatch(ConstArrayDefaultMismatchCertificate),
    /// Unsatisfiable (`QF_ALIA`): equality of finite store chains over the same
    /// `(Array Int Int)` base forces a visible write to equal an untouched base
    /// read, contradicting an asserted disequality. The checker re-scans the
    /// original assertions and re-matches the exact certificate.
    UnsatStoreChainReadback(StoreChainReadbackCertificate),
    /// Unsatisfiable (`QF_AX`): same-index reciprocal store equalities force a
    /// base-array equality that contradicts an asserted array disequality. The
    /// checker re-scans the original assertions and re-matches the exact
    /// certificate.
    UnsatCrossStoreArrayDisequality(CrossStoreArrayDisequalityCertificate),
    /// Unsatisfiable: the query asserts the negation of a small checked term
    /// identity such as `ite true t e = t`. The checker re-scans the original
    /// assertions and re-matches the exact identity before accepting.
    UnsatTermIdentity(TermIdentityRefutationCertificate),
    /// Unsatisfiable: one original assertion normalizes to Boolean `false` under
    /// a small checked propositional simplifier. The checker re-scans the
    /// original assertions and re-runs the same normalizer before accepting.
    UnsatBoolSimplification(BoolSimplificationRefutationCertificate),
    /// Unsatisfiable (`QF_ABV`/`QF_AUFBV`): replacing array-dependent scalar
    /// leaves by fresh unconstrained Bool/BV variables yields a certified-unsat
    /// pure `QF_BV` abstraction. The checker rebuilds the abstraction from the
    /// original assertions and re-runs the pure BV certificate route.
    UnsatBvAbstraction(BvAbstractionRefutationCertificate),
    /// Unsatisfiable (`QF_AUFBV`): a guarded aligned write-chain commutation
    /// refutation. The checker confirms a generated byte-store chain writes two
    /// aligned words in opposite orders; the ranges are disjoint or identical
    /// with identical byte values, so the asserted disequality is impossible.
    UnsatAlignedWriteChainCommutation(AlignedWriteChainCommutationCertificate),
    /// Unsatisfiable (`QF_AUFBV`): a guarded two-byte memcpy refutation. The
    /// checker confirms no-wrap/no-overlap guards for `[src,src+2)` and
    /// `[dst,dst+2)`, a `j < 2` guard, and a two-store copy whose destination
    /// read is asserted different from the matching original source read.
    UnsatTwoByteMemcpy(TwoByteMemcpyRefutationCertificate),
    /// Unsatisfiable (`QF_AUFBV`): a guarded two-element bubble-sort
    /// refutation. The checker confirms the output cells are the conditional
    /// swap/min-max of the two original cells, the in-range guard restricts the
    /// arbitrary read to those cells, and the query asserts that read differs
    /// from both outputs.
    UnsatTwoElementBubbleSort(TwoElementBubbleSortCertificate),
    /// Unsatisfiable (`QF_AUFBV`): a guarded two-element selection-sort
    /// refutation. The checker confirms the generated min-index store pattern,
    /// the in-range read guard, the sortedness bit, and the two disequalities
    /// against the sorted cells.
    UnsatTwoElementSelectionSort(TwoElementSelectionSortCertificate),
    /// Unsatisfiable (`QF_AUFBV`): a two-cell XOR-swap permutation refutation.
    /// The checker confirms the final ordinary-swap array and XOR-swap array
    /// are the same two nested swaps over the same base array.
    UnsatTwoCellXorSwap(TwoCellXorSwapCertificate),
    /// Unsatisfiable (`QF_AUFBV`): a guarded two-byte XOR-swap round-trip
    /// refutation. The checker confirms two disjoint byte ranges are XOR-swapped
    /// twice and the final memory is asserted different from the original.
    UnsatTwoByteXorSwapRoundtrip(TwoByteXorSwapRoundtripCertificate),
    /// Unsatisfiable (`QF_AUFBV`): a generated 16-element binary-search miss
    /// refutation. The checker confirms the stored array is asserted sorted at
    /// every adjacent concrete index and that all generated probes are asserted
    /// different from the searched value.
    UnsatBinarySearch16(BinarySearch16Certificate),
    /// Unsatisfiable (`QF_AUFBV`): a generated five-cycle bounded FIFO
    /// equivalence refutation. The checker re-generates the exact unrolled
    /// transition equality bits and independently checks the finite FIFO
    /// equivalence theorem for the benchmark bound.
    UnsatFifoBc04(FifoBc04Certificate),
    /// Unsatisfiable (`QF_S`/`QF_SLIA` regex membership): a **kernel-checked
    /// derivative-emptiness** refutation (#44/#52). A single-variable membership
    /// class `x ∈ ⋂Rᵢ ∖ ⋃Nⱼ` is certified empty by a complete, nullable-free,
    /// re-checked derivative closure; the carried `lean_module` is the reconstruction
    /// of that certificate to a kernel-`infer`-checked Lean `False`.
    ///
    /// Regexes are **not** representable in the `axeyum-ir` term arena — they live in
    /// the parser's [`MembershipProblem`](axeyum_smtlib::MembershipProblem) side
    /// channel — so unlike the arena-scanning certificates above, [`Evidence::check`]
    /// re-derives this one from the self-contained
    /// [`membership`](Evidence::UnsatRegexEmptiness::membership) object (ignoring the
    /// bounded/empty arena view), never trusting the stored module string. This is the
    /// transferable, checkable counterpart of the bare-but-sound
    /// [`Evidence::Unsat(None)`](Evidence::Unsat) that
    /// [`produce_evidence_smtlib`] emits for the yet-uncertified string `unsat`
    /// classes (word clash, concat/length conflict).
    UnsatRegexEmptiness {
        /// The deciding single-variable membership problem — the self-contained
        /// re-derivation input for [`Evidence::check`].
        membership: axeyum_strings::Membership,
        /// The kernel-checked Lean `False` module reconstructed from the emptiness
        /// certificate; an output artifact, re-derived (not trusted) on re-check.
        lean_module: String,
    },
    /// Unsatisfiable (`QF_S`/`QF_SLIA` word equations): a **self-checking Alethe**
    /// word-clash refutation (ADR-0053/0061). A pure word-equation-and-disequation
    /// system is refuted by a checked derivation whose Alethe proof
    /// ([`WordClashCertificate`](crate::WordClashCertificate)) is **self-contained** —
    /// it carries its own commands, premise core, and element sort key, and
    /// [`Evidence::check`] re-runs the Alethe replay to the empty clause with no arena
    /// (a tampered clause/premise/constant/rule fails). This is the word-clash
    /// counterpart of [`Evidence::UnsatRegexEmptiness`] and the sibling upgrade of the
    /// bare [`Evidence::Unsat(None)`](Evidence::Unsat) for the word-only string
    /// fragment.
    UnsatWordClash(crate::WordClashCertificate),
    /// Unsatisfiable (`QF_S`/`QF_SLIA`/`QF_SEQ` length fragment): a length /
    /// code-point abstraction plus a Farkas-style linear refutation.
    ///
    /// Every string term becomes an integer length variable keyed on its SOURCE
    /// NAME, the handful of theory lemmas the argument uses are named
    /// individually (`|x| >= 0`, `|u| = |v|` from an asserted word equality,
    /// `|x| >= 1` from `x != ""`, and the `str.to_code` range), and the
    /// refutation is one nonnegative combination per case-split branch.
    ///
    /// Self-contained like [`Evidence::UnsatWordClash`] and
    /// [`Evidence::UnsatRegexEmptiness`] (ADR-0061), and for the same reason: the
    /// flat arena view of a string script is the bounded packed-BV encoding, not
    /// the query. The certificate carries the script's own top-level commands, and
    /// [`Evidence::check`] re-derives the premises from them before re-deriving
    /// the arithmetic — a lemma the query does not license is rejected before any
    /// multiplier is read.
    ///
    /// When `lean_module` is present the refutation is ALSO backed by a
    /// kernel-checked Lean proof over the CONSTRUCTED integers — re-derived, not
    /// read back, on [`Evidence::check`] (the stored string is never trusted).
    /// It is `None` for a certificate the reconstruction declines (a case split,
    /// or a combination too large to build), and that is not a weaker
    /// certificate: the arithmetic re-derivation is the same either way.
    UnsatStringLength {
        /// The re-derivable length/code-point refutation.
        certificate: StringLengthRefutationCertificate,
        /// The rendered Lean module, when the reconstruction succeeded.
        lean_module: Option<String>,
    },
    /// Undecided, with the classified reason.
    Unknown(UnknownReason),
}

/// An artifact a checker outside this process can read.
///
/// The distinction that matters for this project's identity claim: evidence can
/// be fully re-validated and still only by calling back into axeyum's own Rust,
/// which is a much weaker statement than "an independent checker read it". Only
/// these two forms leave the process.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PortableArtifact {
    /// DRAT, checkable by `check_drat` here and by external `drat-trim`.
    Drat,
    /// Alethe, checkable by Carcara.
    Alethe,
}

impl PortableArtifact {
    /// The stable label for artifacts and summaries.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            PortableArtifact::Drat => "drat",
            PortableArtifact::Alethe => "alethe",
        }
    }
}

impl Evidence {
    /// Stable short label for this evidence variant.
    ///
    /// Does this evidence carry an artifact a checker **outside this process**
    /// can read?
    ///
    /// This exists because the number everyone quoted was counted from
    /// [`Evidence::kind_label`], and labels are not artifacts. The 2026-08-21
    /// gap analysis reported "only 11 of 129 unsat (8.5%) produce an artifact an
    /// external checker can read", derived by matching kind strings against
    /// `unsat-drat` and the Alethe kinds. But `BoundedIntBlastCertificate`
    /// carries a full DRAT refutation of its bit-blasted CNF in `bv_proof`,
    /// re-checkable by `check_drat`, and its label reads
    /// `unsat-bounded-int-blast`. So do `ArithDpllRefutation` and three
    /// quantified-BV certificates. The metric undercounted the thing it existed
    /// to measure, and did so in the direction that made the project look worse.
    ///
    /// The wildcard below **undercounts by construction**: a new proof-carrying
    /// variant returns `None` until an arm is added. That is the same defect one
    /// level down, so it is not left to vigilance — see the test named in this
    /// module that fails when a certificate gains an `UnsatProof` field without
    /// an arm here.
    ///
    /// **The Alethe arms OVERCOUNTED by construction until 2026-08-21**, which is
    /// the same error in the other direction and the more dangerous one. Every
    /// [`Evidence::UnsatAletheProof`] was reported portable regardless of the rule
    /// names inside it, and the `QF_ABV` emitter's array step was named
    /// `read_over_write_same` — an axeyum-internal name Carcara answers with
    /// `unknown rule`, i.e. `invalid`, not merely `holey`. Measured against
    /// `references/carcara` at `6624ea80`: same problem, same proof, rule renamed
    /// to Carcara's own `arrays_idx`, `valid`. So the Alethe arms now decide from
    /// the **rule vocabulary of the artifact** via
    /// [`axeyum_cnf::non_carcara_checked_rules`], exactly as the `lia_generic`
    /// exclusion below does for one rule by hand. A name-based judgement of
    /// portability is what produced both the 1.75x undercount this function was
    /// written to fix and this overcount.
    #[must_use]
    pub fn portable_artifact(&self) -> Option<PortableArtifact> {
        /// An Alethe artifact is externally checkable only if **every** rule it
        /// names is one Carcara checks. One unknown rule makes the whole proof
        /// `invalid` to the external checker, so this is an all-or-nothing test,
        /// not a proportion.
        fn alethe_if_carcara_vocabulary(proof: &[AletheCommand]) -> Option<PortableArtifact> {
            axeyum_cnf::non_carcara_checked_rules(proof)
                .is_empty()
                .then_some(PortableArtifact::Alethe)
        }

        match self {
            // DRAT: checkable by `check_drat` in-tree and by external
            // `drat-trim` out of tree (verified with a negative control — a
            // tampered proof is rejected).
            Evidence::Unsat(Some(_))
            | Evidence::UnsatBoundedIntBlast(_)
            | Evidence::UnsatArithDpll(_)
            | Evidence::UnsatBvAlternationCounterexample(_)
            | Evidence::UnsatBvConjunctiveUniversalInstance(_)
            | Evidence::UnsatBvPositiveUniversalInstanceSet(_) => Some(PortableArtifact::Drat),
            // Alethe: checkable by Carcara, a Rust Alethe checker — but only
            // when every rule in the artifact is one Carcara checks.
            //
            // `UnsatGuardedQuantAletheProof` reaches the same gate rather than a
            // blanket `Some`: its refutation is `forall_inst_guarded` (an axeyum
            // hook rule Carcara has never heard of) plus `lia_generic` (which
            // Carcara accepts only by holing it), so the gate reports it
            // internal-only. It was counted as portable before this change.
            //
            // `UnsatArithAletheProof` stays EXCLUDED as a variant. Its QF_LIA
            // route emits `lia_generic`, a rule Carcara has no checker for and
            // treats as a hole; the QF_LRA route's `la_generic` IS checked, but
            // routing the variant through the vocabulary gate would widen what
            // this function claims on the strength of a rule-name list alone,
            // with no Carcara crosscheck behind it for this variant. Widen it
            // when there is one.
            Evidence::UnsatAletheProof(proof) => alethe_if_carcara_vocabulary(proof),
            Evidence::UnsatGuardedQuantAletheProof { proof, .. } => {
                alethe_if_carcara_vocabulary(proof)
            }
            _ => None,
        }
    }

    /// These labels are intended for SDK/UI summaries and artifact metadata.
    /// They are deliberately independent of Rust `Debug` formatting.
    #[must_use]
    pub const fn kind_label(&self) -> &'static str {
        match self {
            Evidence::Sat(_) => "sat-model",
            // `Unsat(None)` carries NO proof, so it must not be labelled by one.
            // Collapsing both arms onto "unsat-drat" advertised a DRAT refutation
            // that does not exist -- and this label is what artifact metadata and
            // UI summaries print, so the fabrication propagated outward. Found by
            // a fact-extraction lane whose result line read
            // `kind=unsat-drat certified=0`: self-contradictory, since a DRAT
            // proof is by definition a certificate.
            Evidence::Unsat(Some(_)) => "unsat-drat",
            Evidence::Unsat(None) => "unsat-uncertified",
            Evidence::UnsatAletheProof(_) => "unsat-alethe",
            Evidence::UnsatArithAletheProof(_) => "unsat-arith-alethe",
            Evidence::UnsatGuardedQuantAletheProof { .. } => "unsat-guarded-quant-alethe",
            Evidence::UnsatIntEuclideanResidue(_) => "unsat-int-euclidean-residue",
            Evidence::UnsatIntAffineGrowth(_) => "unsat-int-affine-growth",
            Evidence::UnsatIntNestedXor(_) => "unsat-int-nested-xor",
            Evidence::UnsatClosedUniversalCounterexample(_) => {
                "unsat-closed-universal-counterexample"
            }
            Evidence::UnsatVacuousExistsUniversalCounterexample(_) => {
                "unsat-vacuous-exists-universal-counterexample"
            }
            Evidence::UnsatNegatedExistentialWitness(_) => "unsat-negated-existential-witness",
            Evidence::UnsatBvAlternationCounterexample(_) => "unsat-bv-alternation-counterexample",
            Evidence::UnsatBvConjunctiveUniversalInstance(_) => {
                "unsat-bv-conjunctive-universal-instance"
            }
            Evidence::UnsatBvPositiveUniversalInstanceSet(_) => {
                "unsat-bv-positive-universal-instance-set"
            }
            Evidence::UnsatBvPairedExistentialTransfer(_) => "unsat-bv-paired-existential-transfer",
            Evidence::UnsatEqualityPartition(_) => "unsat-equality-partition",
            Evidence::UnsatQuantifiedCounterexampleCover(_) => {
                "unsat-quantified-counterexample-cover"
            }
            Evidence::UnsatQuantInstanceSet(_) => "unsat-quant-instance-set",
            Evidence::UnsatTermLevel { .. } => "unsat-term-level",
            Evidence::UnsatFiniteDomainEnum { .. } => "unsat-finite-domain-enum",
            Evidence::UnsatBvDefinedEnum(_) => "unsat-bv-defined-enum",
            Evidence::UnsatBvForallNonconstant(_) => "unsat-bv-forall-nonconstant",
            Evidence::UnsatBvUfLocal(_) => "unsat-bv-uf-local",
            Evidence::UnsatSetCardinality(_) => "unsat-set-cardinality",
            Evidence::UnsatFarkas(_) => "unsat-farkas",
            Evidence::UnsatLraDpll(_) => "unsat-lra-dpll",
            Evidence::UnsatArithDpll(_) => "unsat-arith-dpll",
            Evidence::UnsatSos { .. } => "unsat-sos",
            Evidence::UnsatIntQuadraticNegativeDiscriminant(_) => {
                "unsat-int-quadratic-negative-discriminant"
            }
            Evidence::UnsatIntUnivariatePoly(_) => "unsat-int-univariate-poly",
            Evidence::UnsatNraEvenPower(_) => "unsat-nra-even-power",
            Evidence::UnsatRealZeroProduct(_) => "unsat-real-zero-product",
            Evidence::UnsatRealProduct(_) => "unsat-real-product",
            Evidence::UnsatRealHandelman(_) => "unsat-real-handelman",
            Evidence::UnsatMonomialBound(_) => "unsat-monomial-bound",
            Evidence::UnsatDiophantine { .. } => "unsat-diophantine",
            Evidence::UnsatBoundedIntBlast(_) => "unsat-bounded-int-blast",
            Evidence::UnsatFiniteDomainPigeonhole(_) => "unsat-finite-domain-pigeonhole",
            Evidence::UnsatBoolUfExhaustive(_) => "unsat-bool-uf-exhaustive",
            Evidence::UnsatBoolEufExhaustive(_) => "unsat-bool-euf-exhaustive",
            Evidence::UnsatBoolEufOnline(_) => "unsat-bool-euf-online",
            Evidence::UnsatUfArithCongruence(_) => "unsat-uf-arith-congruence",
            Evidence::UnsatDatatypeStructural(_) => "unsat-datatype-structural",
            Evidence::UnsatFiniteArrayExtensionality(_) => "unsat-finite-array-extensionality",
            Evidence::UnsatBoolArrayReadCollapse(_) => "unsat-bool-array-read-collapse",
            Evidence::UnsatArrayAxiom(_) => "unsat-array-axiom",
            Evidence::UnsatConstArrayDefaultMismatch(_) => "unsat-const-array-default-mismatch",
            Evidence::UnsatStoreChainReadback(_) => "unsat-store-chain-readback",
            Evidence::UnsatCrossStoreArrayDisequality(_) => "unsat-cross-store-array-disequality",
            Evidence::UnsatTermIdentity(_) => "unsat-term-identity",
            Evidence::UnsatBoolSimplification(_) => "unsat-bool-simplification",
            Evidence::UnsatBvAbstraction(_) => "unsat-bv-abstraction",
            Evidence::UnsatAlignedWriteChainCommutation(_) => {
                "unsat-aligned-write-chain-commutation"
            }
            Evidence::UnsatTwoByteMemcpy(_) => "unsat-two-byte-memcpy",
            Evidence::UnsatTwoElementBubbleSort(_) => "unsat-two-element-bubble-sort",
            Evidence::UnsatTwoElementSelectionSort(_) => "unsat-two-element-selection-sort",
            Evidence::UnsatTwoCellXorSwap(_) => "unsat-two-cell-xor-swap",
            Evidence::UnsatTwoByteXorSwapRoundtrip(_) => "unsat-two-byte-xor-swap-roundtrip",
            Evidence::UnsatBinarySearch16(_) => "unsat-binary-search-16",
            Evidence::UnsatFifoBc04(_) => "unsat-fifo-bc04",
            Evidence::UnsatRegexEmptiness { .. } => "unsat-regex-emptiness",
            Evidence::UnsatWordClash(_) => "unsat-word-clash",
            Evidence::UnsatStringLength { .. } => "unsat-string-length",
            Evidence::Unknown(_) => "unknown",
        }
    }

    /// Independently re-validates this evidence against the original
    /// `assertions`. Returns `true` **only** when a certificate was present and
    /// this run re-derived it.
    ///
    /// This is [`Evidence::check_outcome`] collapsed to a boolean:
    /// `check_outcome(..)? == EvidenceCheck::Verified`. A bare
    /// [`Evidence::Unsat(None)`](Evidence::Unsat) and an [`Evidence::Unknown`]
    /// return **`false`** — there was nothing to check, which is not a pass
    /// (ADR-0384; before that fix they returned `true`, so `if
    /// evidence.check(..)? { … }` was a green gate over an empty set). Prefer
    /// `check_outcome` when the caller needs to tell "nothing to check" apart
    /// from "checked and failed" — for instance to keep an uncertified-but-sound
    /// `unsat` while still alarming on a bad certificate.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Backend`] if a `sat` replay evaluates to a
    /// non-Boolean (an internal invariant violation) or a stored certificate
    /// fails to re-parse.
    pub fn check(&self, arena: &TermArena, assertions: &[TermId]) -> Result<bool, SolverError> {
        Ok(self.check_outcome(arena, assertions)?.is_verified())
    }

    /// Independently re-validates this evidence against the original
    /// `assertions`, returning the **three-valued** [`EvidenceCheck`] outcome
    /// (ADR-0384).
    ///
    /// [`EvidenceCheck::Verified`] is the only outcome that means a certificate
    /// was re-derived this run. Evidence that carries no certificate (a bare
    /// `unsat`, an `unknown`), and evidence with no faithful subject to check
    /// against (a `sat` model against an empty assertion list), is
    /// [`EvidenceCheck::NothingToCheck`] with the reason. A certificate that is
    /// present and does not hold up is [`EvidenceCheck::Failed`].
    ///
    /// The certificates that are *self-contained* — [`Evidence::UnsatWordClash`],
    /// [`Evidence::UnsatRegexEmptiness`] and [`Evidence::UnsatStringLength`],
    /// which carry their own premises and
    /// deliberately ignore `(arena, assertions)` (ADR-0061) — are re-derived
    /// here regardless of the arena view, so they still report `Verified`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Backend`] if a `sat` replay evaluates to a
    /// non-Boolean (an internal invariant violation) or a stored certificate
    /// fails to re-parse.
    pub fn check_outcome(
        &self,
        arena: &TermArena,
        assertions: &[TermId],
    ) -> Result<EvidenceCheck, SolverError> {
        // Cases with nothing to re-validate are answered BEFORE the checker runs:
        // no checker call can turn them into a `Verified`.
        match self {
            Evidence::Unsat(None) => {
                return Ok(EvidenceCheck::NothingToCheck(
                    NoCheckReason::UncertifiedUnsat,
                ));
            }
            Evidence::Unknown(_) => {
                return Ok(EvidenceCheck::NothingToCheck(NoCheckReason::Undecided));
            }
            // A model replayed against zero assertions passes vacuously — the
            // bounded/empty-view hazard ADR-0061 caught for string scripts. It is
            // reported as nothing-checked, never as a verification.
            Evidence::Sat(_) if assertions.is_empty() => {
                return Ok(EvidenceCheck::NothingToCheck(NoCheckReason::EmptySubject));
            }
            _ => {}
        }
        Ok(if self.recheck_certificate(arena, assertions)? {
            EvidenceCheck::Verified
        } else {
            EvidenceCheck::Failed
        })
    }

    /// Re-runs the certificate-specific checker for this variant. Only called by
    /// [`Evidence::check_outcome`], and only for variants that actually carry a
    /// certificate; `false` means the certificate did not hold up.
    #[allow(clippy::too_many_lines)]
    fn recheck_certificate(
        &self,
        arena: &TermArena,
        assertions: &[TermId],
    ) -> Result<bool, SolverError> {
        match self {
            Evidence::Sat(model) => crate::check_model(arena, assertions, model),
            // Delegated to `UnsatProof::recheck` rather than re-implemented, so
            // the certificate is re-validated by exactly one piece of code
            // (ADR-0613). That routes an LRAT-carrying certificate through the
            // trusted, search-free `check_lrat` with the backward DRAT check as a
            // rejecting-only conjunct, and an LRAT-free one through the forward
            // reference `check_drat` — see that method for the trust argument.
            //
            // Before this delegation existed the two sites re-parsed the same
            // text and ran the forward checker independently, which is how the
            // consumer path silently kept the superlinear checker after the
            // producer stopped using it.
            Evidence::Unsat(Some(proof)) => proof.recheck(),
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
            Evidence::UnsatFiniteDomainEnum { max_total_bits, .. } => {
                match certify_finite_bv_by_enumeration(arena, assertions, *max_total_bits)? {
                    CertifyOutcome::CertifiedUnsat { .. } => Ok(true),
                    CertifyOutcome::Satisfiable(_) => Ok(false),
                    CertifyOutcome::DomainTooLarge { total_bits } => {
                        Err(SolverError::Backend(format!(
                            "finite-domain unsat evidence: domain {total_bits} bits exceeds the \
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
            // Finite-`Int` guarded-quantifier proof: the `forall_inst_guarded`
            // instantiation steps need the combined checker (the arithmetic-aware
            // `lia_generic` kernel PLUS the `forall_inst_guarded` hook closing over
            // the carried universal form, which re-derives each step's substitution
            // and concrete guard truth). The **assume-independent** entry point ALSO
            // verifies every `assume` against the original `assertions` (the universal,
            // each fresh-var abstraction definition, and each original/abstracted side
            // fact) — so the premises are no longer trusted from the emitter; a
            // fabricated premise (or tampered proof) is a clean `Ok(false)`/`Err`,
            // never a silently-accepted bad cert.
            Evidence::UnsatGuardedQuantAletheProof { proof, universal } => {
                check_alethe_lra_guarded_inst_against(universal, proof, arena, assertions).map_err(
                    |e| {
                        SolverError::Backend(format!(
                            "unsat guarded-quantifier Alethe evidence re-check failed: {e}"
                        ))
                    },
                )
            }
            Evidence::UnsatFarkas(certificate) => Ok(certificate.verify()),
            Evidence::UnsatLraDpll(refutation) => refutation.verify(arena),
            Evidence::UnsatArithDpll(refutation) => refutation.verify(arena),
            // Degree-2 SOS/PSD refutation: re-validate the self-contained
            // certificate (rebuilds the Gram matrix from its own terms and confirms
            // the carried LDLᵀ factors reconstruct it with D ≥ 0). When a Lean module
            // is carried, ALSO re-derive it (ADR-0041) — the kernel re-checks the
            // reconstructed proof to `False`; the stored string is never trusted on
            // its own. Both checks must pass.
            Evidence::UnsatSos {
                certificate,
                lean_module,
            } => Ok(check_sos_evidence(
                arena,
                assertions,
                certificate,
                lean_module.is_some(),
            )),
            Evidence::UnsatIntQuadraticNegativeDiscriminant(certificate) => Ok(
                crate::nia_square::check_int_quadratic_negative_discriminant_refutation(
                    arena,
                    assertions,
                    certificate,
                ),
            ),
            Evidence::UnsatIntUnivariatePoly(certificate) => {
                Ok(crate::nia_univariate_cert::check_int_univariate_refutation(
                    arena,
                    assertions,
                    certificate,
                ))
            }
            Evidence::UnsatRealZeroProduct(certificate) => Ok(
                crate::nra_zero_product_cert::check_real_zero_product_refutation(
                    arena,
                    assertions,
                    certificate,
                ),
            ),
            Evidence::UnsatRealProduct(certificate) => {
                Ok(crate::nra_product_cert::check_real_product_refutation(
                    arena,
                    assertions,
                    certificate,
                ))
            }
            Evidence::UnsatRealHandelman(certificate) => {
                Ok(crate::nra_handelman_cert::check_handelman_refutation(
                    arena,
                    assertions,
                    certificate,
                ))
            }
            Evidence::UnsatMonomialBound(certificate) => Ok(
                crate::nra_monomial_bound_cert::check_monomial_bound_refutation(
                    arena,
                    assertions,
                    certificate,
                ),
            ),
            Evidence::UnsatDiophantine {
                equalities,
                certificate,
                lean_module,
            } => Ok(check_diophantine_evidence(
                arena,
                assertions,
                equalities,
                certificate,
                lean_module.as_ref(),
            )),
            Evidence::UnsatBoundedIntBlast(certificate) => certificate.recheck(arena, assertions),
            Evidence::UnsatBvAlternationCounterexample(certificate) => {
                crate::quant_bv_alternation_cert::check_bv_alternation_counterexample(
                    arena,
                    assertions,
                    certificate,
                )
            }
            Evidence::UnsatNegatedExistentialWitness(certificate) => Ok(
                crate::quant_negated_exists_cert::check_negated_existential_witness(
                    arena,
                    assertions,
                    certificate,
                ),
            ),
            Evidence::UnsatVacuousExistsUniversalCounterexample(certificate) => Ok(
                crate::quant_vacuous_exists_counterexample_cert::check_vacuous_exists_universal_counterexample(
                    arena,
                    assertions,
                    certificate,
                ),
            ),
            Evidence::UnsatBvConjunctiveUniversalInstance(certificate) => {
                crate::quant_bv_conjunctive_cert::check_bv_conjunctive_universal_instance(
                    arena,
                    assertions,
                    certificate,
                )
            }
            Evidence::UnsatBvPositiveUniversalInstanceSet(certificate) => {
                crate::quant_bv_instance_set_cert::check_bv_positive_universal_instance_set(
                    arena,
                    assertions,
                    certificate,
                )
            }
            Evidence::UnsatQuantInstanceSet(certificate) => {
                // The replay re-eliminates existentials and reconstructs
                // instances, so it needs a mutable arena. Clone rather than
                // mutate the caller's: those skolem witnesses and rebuilt terms
                // must not leak into a later sat model. The clone need not
                // contain anything from the producing run -- the certificate
                // names only the query's own terms and positions.
                let mut scratch = arena.clone();
                crate::quant_instance_set_cert::check_quantifier_instance_set(
                    &mut scratch,
                    assertions,
                    certificate,
                    &SolverConfig::default(),
                )
            }
            Evidence::UnsatBvPairedExistentialTransfer(certificate) => {
                crate::quant_bv_paired_exists_cert::check_bv_paired_existential_transfer(
                    arena,
                    assertions,
                    certificate,
                )
            }
            Evidence::UnsatFiniteDomainPigeonhole(_)
            | Evidence::UnsatBoolUfExhaustive(_)
            | Evidence::UnsatBoolEufExhaustive(_)
            | Evidence::UnsatBoolEufOnline(_)
            | Evidence::UnsatUfArithCongruence(_)
            | Evidence::UnsatDatatypeStructural(_)
            | Evidence::UnsatFiniteArrayExtensionality(_)
            | Evidence::UnsatBoolArrayReadCollapse(_)
            | Evidence::UnsatNraEvenPower(_)
            | Evidence::UnsatBvDefinedEnum(_)
            | Evidence::UnsatBvForallNonconstant(_)
            | Evidence::UnsatIntEuclideanResidue(_)
            | Evidence::UnsatIntAffineGrowth(_)
            | Evidence::UnsatIntNestedXor(_)
            | Evidence::UnsatClosedUniversalCounterexample(_)
            | Evidence::UnsatEqualityPartition(_)
            | Evidence::UnsatQuantifiedCounterexampleCover(_)
            | Evidence::UnsatBvUfLocal(_)
            | Evidence::UnsatSetCardinality(_)
            | Evidence::UnsatArrayAxiom(_)
            | Evidence::UnsatConstArrayDefaultMismatch(_)
            | Evidence::UnsatStoreChainReadback(_)
            | Evidence::UnsatCrossStoreArrayDisequality(_)
            | Evidence::UnsatTermIdentity(_)
            | Evidence::UnsatBoolSimplification(_)
            | Evidence::UnsatBvAbstraction(_)
            | Evidence::UnsatAlignedWriteChainCommutation(_)
            | Evidence::UnsatTwoByteMemcpy(_)
            | Evidence::UnsatTwoElementBubbleSort(_)
            | Evidence::UnsatTwoElementSelectionSort(_)
            | Evidence::UnsatTwoCellXorSwap(_)
            | Evidence::UnsatTwoByteXorSwapRoundtrip(_)
            | Evidence::UnsatBinarySearch16(_)
            | Evidence::UnsatFifoBc04(_) => {
                Ok(check_direct_structural_evidence(self, arena, assertions))
            }
            // Regex membership emptiness (#44/#52): re-derive the certificate from the
            // self-contained `Membership` from first principles and re-run the kernel
            // `infer`/`def_eq False` check inside the reconstructor — the stored module
            // string is never trusted on its own. Regexes are not in the term arena, so
            // this ignores `arena`/`assertions` (they are the bounded/empty flat view).
            // A reconstruction decline is a clean `Ok(false)`, never a bad certificate.
            Evidence::UnsatRegexEmptiness { membership, .. } => {
                Ok(crate::reconstruct_regex_emptiness_to_lean_module(membership).is_ok())
            }
            // Self-checking Alethe word-clash refutation: re-run the embedded proof to
            // the empty clause (arena-free; the certificate carries its own premises and
            // element sort key). A tampered proof fails here — never trusted as-is.
            Evidence::UnsatWordClash(certificate) => Ok(certificate.check()),
            // Length/code-point abstraction refutation: stage 1 re-derives the
            // premise conjuncts from the carried source commands and binds every
            // lemma instance to the conjunct that licenses it; stage 2 re-derives
            // the Farkas combination. Arena-free for the same reason as the two
            // above — the flat view of a string script is not the query.
            //
            // A carried Lean module is re-derived from the same certificate and
            // must succeed; the stored string is never read back. A certificate
            // that carries none is checked by the arithmetic alone, so a decline
            // at production time cannot turn into a check failure here.
            Evidence::UnsatStringLength {
                certificate,
                lean_module,
            } => Ok(
                crate::string_length_cert::check_string_length_refutation(certificate)
                    && (lean_module.is_none()
                        || crate::reconstruct_string_length_to_lean_module(certificate).is_ok()),
            ),
            // Nothing to re-validate. `check_outcome` answers these before ever
            // calling here; `false` (never `true`) is the conservative value if
            // that guard is ever bypassed, so no route can resurrect the
            // "vacuously checked" behavior ADR-0384 removed.
            Evidence::Unsat(None) | Evidence::Unknown(_) => Ok(false),
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
                | Evidence::UnsatGuardedQuantAletheProof { .. }
                | Evidence::UnsatTermLevel { .. }
                | Evidence::UnsatFiniteDomainEnum { .. }
                | Evidence::UnsatBvDefinedEnum(_)
                | Evidence::UnsatBvForallNonconstant(_)
                | Evidence::UnsatIntEuclideanResidue(_)
                | Evidence::UnsatIntAffineGrowth(_)
                | Evidence::UnsatIntNestedXor(_)
                | Evidence::UnsatClosedUniversalCounterexample(_)
                | Evidence::UnsatVacuousExistsUniversalCounterexample(_)
                | Evidence::UnsatNegatedExistentialWitness(_)
                | Evidence::UnsatBvAlternationCounterexample(_)
                | Evidence::UnsatBvConjunctiveUniversalInstance(_)
                | Evidence::UnsatBvPositiveUniversalInstanceSet(_)
                | Evidence::UnsatBvPairedExistentialTransfer(_)
                | Evidence::UnsatEqualityPartition(_)
                | Evidence::UnsatQuantifiedCounterexampleCover(_)
                | Evidence::UnsatQuantInstanceSet(_)
                | Evidence::UnsatBvUfLocal(_)
                | Evidence::UnsatSetCardinality(_)
                | Evidence::UnsatFarkas(_)
                | Evidence::UnsatLraDpll(_)
                | Evidence::UnsatArithDpll(_)
                | Evidence::UnsatSos { .. }
                | Evidence::UnsatIntQuadraticNegativeDiscriminant(_)
                | Evidence::UnsatIntUnivariatePoly(_)
                | Evidence::UnsatNraEvenPower(_)
                | Evidence::UnsatRealZeroProduct(_)
                | Evidence::UnsatRealProduct(_)
                | Evidence::UnsatRealHandelman(_)
                | Evidence::UnsatMonomialBound(_)
                | Evidence::UnsatDiophantine { .. }
                | Evidence::UnsatBoundedIntBlast(_)
                | Evidence::UnsatFiniteDomainPigeonhole(_)
                | Evidence::UnsatBoolUfExhaustive(_)
                | Evidence::UnsatBoolEufExhaustive(_)
                | Evidence::UnsatBoolEufOnline(_)
                | Evidence::UnsatUfArithCongruence(_)
                | Evidence::UnsatDatatypeStructural(_)
                | Evidence::UnsatFiniteArrayExtensionality(_)
                | Evidence::UnsatBoolArrayReadCollapse(_)
                | Evidence::UnsatArrayAxiom(_)
                | Evidence::UnsatConstArrayDefaultMismatch(_)
                | Evidence::UnsatStoreChainReadback(_)
                | Evidence::UnsatCrossStoreArrayDisequality(_)
                | Evidence::UnsatTermIdentity(_)
                | Evidence::UnsatBoolSimplification(_)
                | Evidence::UnsatBvAbstraction(_)
                | Evidence::UnsatAlignedWriteChainCommutation(_)
                | Evidence::UnsatTwoByteMemcpy(_)
                | Evidence::UnsatTwoElementBubbleSort(_)
                | Evidence::UnsatTwoElementSelectionSort(_)
                | Evidence::UnsatTwoCellXorSwap(_)
                | Evidence::UnsatTwoByteXorSwapRoundtrip(_)
                | Evidence::UnsatBinarySearch16(_)
                | Evidence::UnsatFifoBc04(_)
                | Evidence::UnsatRegexEmptiness { .. }
                | Evidence::UnsatWordClash(_)
                | Evidence::UnsatStringLength { .. }
        )
    }
}

fn check_direct_structural_evidence(
    evidence: &Evidence,
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    match evidence {
        Evidence::UnsatFiniteDomainPigeonhole(cert) => {
            check_uf_pigeonhole_evidence(arena, assertions, cert)
        }
        Evidence::UnsatBoolUfExhaustive(cert) => {
            check_bool_uf_exhaustive_evidence(arena, assertions, cert)
        }
        Evidence::UnsatBoolEufExhaustive(cert) => {
            check_bool_euf_exhaustive_evidence(arena, assertions, cert)
        }
        Evidence::UnsatBoolEufOnline(cert) => {
            check_bool_euf_online_evidence(arena, assertions, *cert)
        }
        Evidence::UnsatUfArithCongruence(cert) => {
            check_uf_arith_congruence_evidence(arena, assertions, cert)
        }
        Evidence::UnsatDatatypeStructural(cert) => {
            check_datatype_structural_evidence(arena, assertions, cert)
        }
        Evidence::UnsatFiniteArrayExtensionality(cert) => {
            check_finite_array_extensionality_evidence(arena, assertions, cert)
        }
        Evidence::UnsatBoolArrayReadCollapse(cert) => {
            check_bool_array_read_collapse_evidence(arena, assertions, cert)
        }
        Evidence::UnsatNraEvenPower(cert) => check_nra_even_power_evidence(arena, assertions, cert),
        Evidence::UnsatBvDefinedEnum(cert) => {
            check_bv_defined_enum_evidence(arena, assertions, cert)
        }
        Evidence::UnsatBvForallNonconstant(cert) => {
            check_bv_forall_nonconstant_evidence(arena, assertions, cert)
        }
        Evidence::UnsatIntEuclideanResidue(cert) => {
            check_int_euclidean_residue_evidence(arena, assertions, cert)
        }
        Evidence::UnsatIntAffineGrowth(cert) => {
            check_int_affine_growth_evidence(arena, assertions, cert)
        }
        Evidence::UnsatIntNestedXor(cert) => check_int_nested_xor_evidence(arena, assertions, cert),
        Evidence::UnsatClosedUniversalCounterexample(cert) => {
            crate::quant_closed_counterexample_cert::check_closed_universal_counterexample(
                arena, assertions, cert,
            )
        }
        Evidence::UnsatEqualityPartition(cert) => {
            crate::quant_eq_partition_cert::check_equality_partition_refutation(
                arena, assertions, cert,
            )
        }
        Evidence::UnsatQuantifiedCounterexampleCover(cert) => {
            crate::quant_counterexample_cover::check_quantified_counterexample_cover(
                arena, assertions, cert,
            )
        }
        Evidence::UnsatBvUfLocal(cert) => check_bv_uf_local_evidence(arena, assertions, cert),
        Evidence::UnsatSetCardinality(cert) => {
            check_set_cardinality_evidence(arena, assertions, cert)
        }
        Evidence::UnsatArrayAxiom(cert) => check_array_axiom_evidence(arena, assertions, cert),
        Evidence::UnsatConstArrayDefaultMismatch(cert) => {
            check_const_array_default_mismatch_evidence(arena, assertions, cert)
        }
        Evidence::UnsatStoreChainReadback(cert) => {
            check_store_chain_readback_evidence(arena, assertions, cert)
        }
        Evidence::UnsatCrossStoreArrayDisequality(cert) => {
            check_cross_store_array_disequality_evidence(arena, assertions, cert)
        }
        Evidence::UnsatTermIdentity(cert) => check_term_identity_evidence(arena, assertions, cert),
        Evidence::UnsatBoolSimplification(cert) => {
            check_bool_simplification_evidence(arena, assertions, *cert)
        }
        Evidence::UnsatBvAbstraction(cert) => {
            check_bv_abstraction_evidence(arena, assertions, cert)
        }
        Evidence::UnsatAlignedWriteChainCommutation(cert) => {
            check_aligned_write_chain_commutation_evidence(arena, assertions, cert)
        }
        Evidence::UnsatTwoByteMemcpy(cert) => {
            check_two_byte_memcpy_evidence(arena, assertions, cert)
        }
        Evidence::UnsatTwoElementBubbleSort(cert) => {
            check_two_element_bubble_sort_evidence(arena, assertions, cert)
        }
        Evidence::UnsatTwoElementSelectionSort(cert) => {
            check_two_element_selection_sort_evidence(arena, assertions, cert)
        }
        Evidence::UnsatTwoCellXorSwap(cert) => {
            check_two_cell_xor_swap_evidence(arena, assertions, cert)
        }
        Evidence::UnsatTwoByteXorSwapRoundtrip(cert) => {
            check_two_byte_xor_swap_roundtrip_evidence(arena, assertions, cert)
        }
        Evidence::UnsatBinarySearch16(cert) => {
            check_binary_search16_evidence(arena, assertions, cert)
        }
        Evidence::UnsatFifoBc04(cert) => check_fifo_bc04_evidence(arena, assertions, cert),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// GAP #6 OF `docs/plan/gap-analysis-smt-solvers-2026-08-21.md`: the checkers
// below that read
//
//     producer(arena, assertions).is_some_and(|fresh| fresh == *cert)
//
// are a DETERMINISM check, not a soundness check. If the producer's recognizer
// matched a satisfiable query it matches it identically on the re-run, and the
// checker whose entire job is to catch a wrong producer agrees with it.
//
// Every remaining one was read and classified on 2026-08-21, because "~30
// checkers re-run the producer" turns out to be three different situations and
// only one of them is the defect:
//
//   (A) THE PRODUCER IS A COMPLETE DECISION PROCEDURE, not a recognizer, so the
//       re-run genuinely re-decides `unsat` over the ORIGINAL assertions.
//       `bool_uf_exhaustive_refutation` enumerates every Boolean assignment and
//       every `Bool^n -> Bool` truth table and returns `None` the moment one
//       satisfies the query; `bool_euf_exhaustive_refutation` enumerates every
//       Boolean-abstraction assignment and requires congruence to kill each;
//       `bool_euf_online_refutation` calls the online EUF solver outright. For
//       these the criticism does not bite the same way: a satisfiable query is
//       refused by the re-run itself. 3 families, 16 instances:
//       `bool-uf-exhaustive` 7, `bool-euf-exhaustive` 6, `bool-euf-online` 3.
//
//   (B) A RECOGNIZER WHOSE CERTIFICATE CARRIES ITS OWN CLAIM. These are the
//       convertible ones: the certificate names terms, sorts, counts or
//       coefficients from which the claim can be re-derived without asking the
//       recognizer anything. Four have been converted so far —
//       `array-axiom` (85 instances), `nra-even-power` (10),
//       `finite-array-extensionality` (4), `finite-domain-pigeonhole` (3);
//       together 102 of the 281 certified `unsat`, 36.3%.
//       18 families / 33 instances remain in this class. Largest first:
//       `bv-forall-nonconstant` (6),
//       `bv-uf-local` (6), `set-cardinality` (4), `term-identity` (3),
//       `const-array-default-mismatch` (1), `store-chain-readback` (1),
//       `bool-array-read-collapse` (1), and the generated array-workload
//       family (`aligned-write-chain-commutation`, `two-byte-memcpy`,
//       `two-element-{bubble,selection}-sort`, `two-cell-xor-swap`,
//       `two-byte-xor-swap-roundtrip`, `binary-search16`).
//
//   (C) A RECOGNIZER WHOSE CERTIFICATE CANNOT EXPRESS ITS CLAIM — 5 families,
//       14 instances. Named here rather than implied away, because a named
//       residual is worth more than a silent one, and because the fix for each
//       is a CERTIFICATE change, not a checker change:
//
//         `uf-arith-congruence` (4) — the certificate is two counts
//           (`arithmetic_assertions`, `congruence_consequents`). Nothing
//           identifies WHICH congruence consequents were used or carries the
//           arithmetic refutation that closed them.
//         `bv-abstraction` (4) — carries `abstracted_terms: Vec<TermId>` and
//           DISCARDS the inner QF_BV evidence that actually establishes the
//           `unsat`. The producer self-checks that evidence and then throws it
//           away. This is the cheapest one to close, and closing it moves 4
//           instances into the externally-checkable DRAT column rather than
//           merely making the internal check honest.
//         `datatype-structural` (3) — carries `branches: u64`. The conflicting
//           merge / acyclicity cycle / distinctness pair is never recorded.
//         `cross-store-array-disequality` (2) — two `TermId`s and a `steps`
//           count; the reciprocal-store chain that derives the base equality is
//           not recorded, so the entailment cannot be replayed.
//         `fifo-bc04` (1) — an `assertion` id plus three compile-time
//           constants; the query test is a whole-instance structural
//           fingerprint against the generated benchmark.
//
//       `bool-euf-online` (3) is in (A) AND has a (C)-grade certificate (a lone
//       `atoms: usize`), so for it the re-run genuinely IS the whole check —
//       which is sound only because the thing re-run is a decision procedure.
//
// The rule the conversions follow, learned the expensive way on the
// array-axiom family: an independent stage placed IN FRONT of the re-run kills
// nothing, because `fresh == *cert` subsumes it. Anything reachable by the
// independent route must be DECIDED by it, with no fall-through.
// ---------------------------------------------------------------------------

/// Was `finite_domain_pigeonhole_refutation(..).is_some_and(|fresh| fresh == *cert)`
/// — a **determinism** check sold as a soundness check. A recognizer that matched
/// a satisfiable query matches it identically on the re-run, so the checker whose
/// entire job is to catch a wrong producer would agree with it.
///
/// It is now decided from the certificate and the query alone. This family's
/// certificate carries enough to make that possible — the function, the claimed
/// domain cardinality, and the pairwise-disequal applications — so the pigeonhole
/// argument is re-derived rather than re-searched. There is deliberately **no
/// fall-through** to the re-run: a guard placed behind `fresh == *cert` is
/// unreachable, because the equality subsumes it, and would then kill no test at
/// all.
fn check_uf_pigeonhole_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &FiniteDomainPigeonholeCertificate,
) -> bool {
    crate::ufbv_finite::certificate_is_finite_domain_pigeonhole(arena, assertions, cert)
}

fn check_bool_uf_exhaustive_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &BoolUfExhaustiveCertificate,
) -> bool {
    crate::ufbv_finite::bool_uf_exhaustive_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_bool_euf_exhaustive_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &BoolEufExhaustiveCertificate,
) -> bool {
    crate::bool_euf::bool_euf_exhaustive_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_bool_euf_online_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: BoolEufOnlineCertificate,
) -> bool {
    crate::bool_euf::bool_euf_online_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == cert)
}

fn check_uf_arith_congruence_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &UfArithCongruenceCertificate,
) -> bool {
    crate::uf_arith::uf_arith_congruence_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_datatype_structural_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &DatatypeStructuralRefutationCertificate,
) -> bool {
    crate::datatype_acyclicity::datatype_structural_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

/// Was `finite_array_extensionality_refutation(..).is_some_and(|fresh| fresh == *cert)`
/// — a **determinism** check, for the same reason as
/// [`check_uf_pigeonhole_evidence`] above.
///
/// It is now decided from the certificate and the query alone: coverage of every
/// index value, membership of every named read equality in the query, the shape
/// of each of those conjuncts, and the array disequality itself. No fall-through
/// to the re-run.
fn check_finite_array_extensionality_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &FiniteArrayExtensionalityCertificate,
) -> bool {
    crate::array_finite::certificate_is_finite_array_extensionality(arena, assertions, cert)
}

fn check_bool_array_read_collapse_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &BoolArrayReadCollapseCertificate,
) -> bool {
    cert.recheck(arena, assertions)
}

/// Was `nra_even_power_refutation(..).is_some_and(|fresh| fresh == *cert)` — a
/// **determinism** check, for the same reason as [`check_uf_pigeonhole_evidence`]
/// above.
///
/// This certificate's claim is entirely local to the conjunct it names, so it is
/// now decided in two stages and the search is never re-run:
///
/// 1. `cert.assertion` is a top-level conjunct of the QUERY. Without this the
///    certificate may name a valid refutation of something the query never
///    asserts, and "¬(impossible)" would refute a satisfiable query.
/// 2. that conjunct really is a negative-even-power-sum refutation, re-derived
///    from the two terms alone.
fn check_nra_even_power_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &NraEvenPowerRefutationCertificate,
) -> bool {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        crate::term_walk::collect_top_binary_conjuncts(arena, assertion, &mut conjuncts);
    }
    if !conjuncts.contains(&cert.assertion) {
        return false;
    }
    crate::nra_even_power::certificate_refutes_its_assertion(arena, cert)
}

fn check_bv_defined_enum_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &BvDefinedEnumRefutationCertificate,
) -> bool {
    crate::bv_defined_enum::bv_defined_enum_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_bv_forall_nonconstant_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &BvForallNonconstantRefutationCertificate,
) -> bool {
    crate::bv_forall_nonconstant::bv_forall_nonconstant_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_int_euclidean_residue_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &IntEuclideanResidueRefutationCertificate,
) -> bool {
    crate::quant_residue_cert::int_euclidean_residue_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_int_affine_growth_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &IntAffineGrowthRefutationCertificate,
) -> bool {
    crate::quant_affine_growth_cert::int_affine_growth_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_int_nested_xor_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &IntNestedXorRefutationCertificate,
) -> bool {
    crate::quant_nested_xor_cert::int_nested_xor_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_bv_uf_local_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &BvUfLocalRefutationCertificate,
) -> bool {
    crate::bv_uf_local::bv_uf_local_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_set_cardinality_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &SetCardinalityRefutationCertificate,
) -> bool {
    crate::set_cardinality::set_cardinality_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

/// The largest certified-`unsat` family in the repository — 85 of 281 instances,
/// 30.2%, measured 2026-08-21 — and until now its check was a re-run of the
/// producer compared for equality.
///
/// That is a **determinism** check, not a soundness check. If
/// `array_axiom_refutation`'s recognizer matched a satisfiable query, it would
/// match it identically on the re-run and `fresh == *cert` would hold; the
/// checker whose job is to catch a wrong producer would agree with it. The
/// certificate cannot help, because it carries three arena-local `TermId`s and a
/// schema tag and nothing a checker could re-derive from.
///
/// So the re-run is kept — it is what binds the certificate to the assertion the
/// search chose — and two independent stages are added on top. Each is decided
/// from the certificate and the arena WITHOUT asking the recognizer anything:
///
/// 1. `is_degenerate` — `lhs == rhs` justifies nothing, and the rendered Lean
///    module for it proves `False` by `rfl` alone. The producer filters this;
///    the checker never did.
/// 2. `certificate_is_axiom_instance` — `lhs = rhs` really is an instance of the
///    schema the certificate names.
///
/// **What is still owed, stated rather than implied.** `ReadCongruence`
/// certificates are not schema matches — they come out of equality facts
/// accumulated across assertions — so stage 2 cannot decide them and they rest
/// on the re-run alone. Likewise the BTOR-derived path, where the named
/// assertion *entails* `¬(lhs = rhs)` rather than stating it:
/// `assertion_states_disequality` decides the stating case and returns `false`
/// for the entailing one. Both residuals are the same shape — an independent
/// checker for facts derived across assertions — and both are real.
fn check_array_axiom_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &ArrayAxiomRefutationCertificate,
) -> bool {
    // A degenerate certificate justifies nothing: its Lean module proves `False`
    // by `rfl` alone, using neither the query nor the array axioms. The producer
    // filters this; the checker never did.
    //
    // Stated plainly, because a guard that cannot fail is worse than none:
    // **deleting this kills no test**, and that is not an oversight. On the
    // independent route stage 2 refuses `lhs == rhs` anyway (`x = x` is not an
    // instance of any array schema), and on the residual route the producer
    // filters degeneracy before the comparison. It is kept as an explicit and
    // cheap precondition on a value that can arrive deserialized from outside
    // this process — but it is subsumed, and the two guards below are the ones
    // carrying the weight.
    if cert.is_degenerate() {
        return false;
    }

    // THE INDEPENDENT ROUTE. Both conditions are decided from the certificate
    // and the query alone, without asking the recognizer anything, so a
    // recognizer that matched a satisfiable query is caught here rather than
    // agreed with.
    //
    // Note what it does NOT do: fall through to the re-run on failure. Anything
    // reachable by this route is decided by it, because a guard that sits behind
    // `fresh == *cert` is unreachable — the equality subsumes it, and both
    // guards then kill no test at all. That is measured, not argued: staged
    // behind the re-run, deleting either of these changed no test result.
    let states_the_disequality =
        crate::array_axiom::assertion_states_disequality(arena, cert.assertion, cert.lhs, cert.rhs);
    let is_a_schema_kind = cert.kind != crate::array_axiom::ArrayAxiomKind::ReadCongruence;
    if is_a_schema_kind && states_the_disequality && assertions.contains(&cert.assertion) {
        // `assertions.contains` is load-bearing and not a formality: without it a
        // certificate may name a VALID axiom instance the query never asserts,
        // and `¬(valid identity)` being unsatisfiable would then "refute" a
        // perfectly satisfiable query.
        return crate::array_axiom::certificate_is_axiom_instance(arena, cert);
    }

    // THE RESIDUAL, named rather than implied. Two shapes reach here and both
    // still rest on re-running the producer and comparing for equality, which is
    // a determinism check and not a soundness check:
    //
    //   * `ReadCongruence` — built from equality facts accumulated ACROSS
    //     assertions, not by matching a schema against two terms, so there is no
    //     two-term claim for stage 2 to decide.
    //   * the BTOR-derived path, where the named assertion *entails*
    //     `¬(lhs = rhs)` through bit-blasted Boolean structure rather than
    //     stating it.
    //
    // Both need the same missing thing: an independent checker for a fact
    // derived across assertions. `corpus_array_axiom_certificates_are_measured_against_both_stages`
    // counts how much of the family is on which side, so this residual is a
    // number rather than a caveat.
    crate::array_axiom::array_axiom_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_const_array_default_mismatch_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &ConstArrayDefaultMismatchCertificate,
) -> bool {
    crate::abv::const_array_default_mismatch_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_store_chain_readback_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &StoreChainReadbackCertificate,
) -> bool {
    crate::abv::store_chain_readback_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_cross_store_array_disequality_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &CrossStoreArrayDisequalityCertificate,
) -> bool {
    crate::abv::cross_store_array_disequality_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_term_identity_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &TermIdentityRefutationCertificate,
) -> bool {
    crate::term_identity::term_identity_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_bool_simplification_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: BoolSimplificationRefutationCertificate,
) -> bool {
    crate::bool_simplify::bool_simplification_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == cert)
}

fn check_bv_abstraction_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &BvAbstractionRefutationCertificate,
) -> bool {
    crate::array_bv_abs::bv_abstraction_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_aligned_write_chain_commutation_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &AlignedWriteChainCommutationCertificate,
) -> bool {
    crate::array_write_chain::aligned_write_chain_commutation_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_two_byte_memcpy_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &TwoByteMemcpyRefutationCertificate,
) -> bool {
    crate::array_memcpy::two_byte_memcpy_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_two_element_bubble_sort_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &TwoElementBubbleSortCertificate,
) -> bool {
    crate::array_sort2::two_element_bubble_sort_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_two_element_selection_sort_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &TwoElementSelectionSortCertificate,
) -> bool {
    crate::array_sort2::two_element_selection_sort_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_two_cell_xor_swap_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &TwoCellXorSwapCertificate,
) -> bool {
    crate::array_xor_swap::two_cell_xor_swap_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_two_byte_xor_swap_roundtrip_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &TwoByteXorSwapRoundtripCertificate,
) -> bool {
    crate::array_xor_swap::two_byte_xor_swap_roundtrip_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_binary_search16_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &BinarySearch16Certificate,
) -> bool {
    crate::array_binary_search::binary_search16_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_fifo_bc04_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &FifoBc04Certificate,
) -> bool {
    crate::array_fifo::fifo_bc04_refutation(arena, assertions).is_some_and(|fresh| fresh == *cert)
}

fn check_sos_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &SosCertificate,
    lean_module_present: bool,
) -> bool {
    if !certificate.verify() {
        return false;
    }
    if lean_module_present {
        // Re-run the immutable SOS→Lean reconstruction; success means the
        // trusted kernel re-accepted a freshly-built proof of `False`.
        return crate::reconstruct::reconstruct_sos_to_lean_module(arena, assertions).is_ok();
    }
    true
}

fn check_diophantine_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    equalities: &[Equality],
    certificate: &DiophantineCertificate,
    lean_module: Option<&String>,
) -> bool {
    if !check_diophantine_certificate(equalities, certificate) {
        return false;
    }
    lean_module.is_none()
        || crate::int_reconstruct::reconstruct_diophantine_to_lean_module(arena, assertions).is_ok()
}

/// Runs the pure-Rust `QF_BV` pipeline on `assertions` and packages the outcome
/// as a self-checking [`EvidenceReport`]: a `sat` model, or one of the `unsat`
/// certificates in **decreasing assurance precedence**, or `unknown`, each with
/// versioned [`Provenance`]. The `unsat` precedence is:
///
/// 1. **term-level enumeration** (≤20 total symbol bits) — trusts only the
///    evaluator, the strongest;
/// 2. **direct structural BV certificates**, including lowered finite-set
///    cardinality contradictions;
/// 3. **Alethe bitblast→CNF→resolution proof** ([`Evidence::UnsatAletheProof`])
///    when the instance is in the driver's fragment — `check_alethe` re-derives
///    the bit-blast itself, so all of bit-blast/Tseitin/SAT-refutation are
///    certified this run;
/// 4. **plain DRAT** ([`Evidence::Unsat`]) otherwise — Tseitin + the SAT
///    refutation are DRAT-checked, but the bit-blast is trusted, not certified.
///
/// # Errors
///
/// Returns [`SolverError`] from the backend or proof export, including a
/// soundness alarm if the backend and proof core disagree.
#[allow(clippy::too_many_lines)] // route dispatch + certificate selection, not one thing growing
pub fn produce_qf_bv_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<EvidenceReport, SolverError> {
    // `config.timeout` is the budget for THIS CALL, not for the decision phase
    // alone (ADR-0384). Fixing the deadline here means proof production spends
    // whatever the decision left over and no more; before this, a hard `unsat`
    // re-ran the entire search uncapped after the timed decision returned.
    let deadline = config
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    let (progress, check_progress) = (
        config.proof_progress.as_ref(),
        config.check_progress.as_ref(),
    );
    let mut backend = SatBvBackend::new();
    let provenance = Provenance::for_query(config, backend.capabilities().name, assertions.len());
    if let Some(cert) = crate::set_cardinality::set_cardinality_refutation(arena, assertions) {
        return Ok(EvidenceReport {
            evidence: Evidence::UnsatSetCardinality(cert),
            provenance,
            trusted_steps: Vec::new(),
        });
    }
    if let Some(cert) = crate::bv_defined_enum::bv_defined_enum_refutation(arena, assertions) {
        return Ok(EvidenceReport {
            evidence: Evidence::UnsatBvDefinedEnum(cert),
            provenance,
            trusted_steps: Vec::new(),
        });
    }
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
    // Was this XOR `unsat` the certifiable pure-Gaussian-level-0 sub-case? The
    // backend stamps `xor_cdcl_fallback_unsat_drat_checked` when its conflict
    // subset's `CNF(S)` carried a `check_drat`-validated DRAT certificate. We then
    // re-derive that certificate independently here (a fresh bit-blast + a fresh
    // `check_drat`) and attach it as real `Evidence::Unsat(Some(_))` with
    // `XorGaussian` certified for this run. If the re-derivation does not validate
    // (it always should for the same query), we fall back to the trusted bare
    // `unsat` below — never a `certified: true` without a validating certificate.
    let xor_cdcl_unsat_certified = backend.last_stats().is_some_and(|s| {
        s.backend
            .iter()
            .any(|(name, value)| name == "xor_cdcl_fallback_unsat_drat_checked" && *value > 0.0)
    });
    let xor_gauss_cert = if matches!(check, CheckResult::Unsat) && xor_cdcl_unsat_certified {
        crate::sat_bv_backend::pure_gauss_xor_unsat_certificate_for_query(arena, assertions)
    } else {
        None
    };
    let (evidence, trusted_steps) = match check {
        CheckResult::Sat(model) => (Evidence::Sat(model), Vec::new()),
        CheckResult::Unknown(reason) => (Evidence::Unknown(reason), Vec::new()),
        CheckResult::Unsat if xor_gauss_cert.is_some() => (
            // Pure-Gaussian-level-0 XOR refutation: the recovered XOR system is
            // inconsistent by Gaussian elimination alone, and the conflict subset
            // `CNF(S)` carries a `check_drat`-validated DRAT certificate (re-derived
            // and re-checked here). bit-blast and Tseitin produced the CNF (trusted,
            // not certified on this route); the XOR-Gaussian step IS certified this
            // run by the attached, re-checkable certificate.
            Evidence::Unsat(xor_gauss_cert),
            trust_steps(&[
                (TrustId::BitBlast, false),
                (TrustId::Tseitin, false),
                (TrustId::XorGaussian, true),
            ]),
        ),
        CheckResult::Unsat if xor_cdcl_unsat => (
            // Search-only XOR refutation: bit-blast and Tseitin produced the CNF
            // (trusted, not certified on this route), and the XOR Gaussian search
            // refuted it without an RUP-checkable proof — the ledgered hole. This
            // is the interleaved CDCL(XOR) case (branching was needed), which is not
            // pure-Gauss-certifiable and stays trusted.
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
                            drat_qf_bv_evidence(
                                arena,
                                assertions,
                                deadline,
                                progress,
                                check_progress,
                            )?
                        }
                    } else {
                        drat_qf_bv_evidence(arena, assertions, deadline, progress, check_progress)?
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
/// `deadline` bounds the **proof-producing SAT search** (ADR-0384). Proof
/// production is a second, independent search over the same formula — on a hard
/// `unsat` it costs as much as the decision did or more — so an unbounded call
/// here silently ignores the caller's `SolverConfig::timeout`. When the deadline
/// is already spent, or expires mid-search, the query is still **decided**: the
/// result is the honest bare [`Evidence::Unsat(None)`](Evidence::Unsat) with
/// `SatRefutation` recorded uncertified. It is never an [`Err`] and never an
/// [`Evidence::Unknown`] — losing a proof must not lose a verdict.
///
/// `progress`, when set, is forwarded to the proof-producing SAT search
/// verbatim (see [`crate::backend::ProofProgress`] /
/// `export_qf_bv_unsat_proof_with_progress`) — a pure observability hook that
/// cannot change which of the three outcomes below is reached, only how often
/// a snapshot is reported while getting there.
///
/// `check_progress`, when set, bounds and observes the CHECKING stage that
/// runs after the search returns `unsat` ([`crate::backend::CheckProgress`] /
/// [`CheckingProgress`] / [`CheckBudget`]) — the stage that had no bound or
/// observability at all before this parameter existed. It shares `deadline`
/// with the search above (checking gets whatever wall-clock budget is left,
/// exactly like the search does relative to `config.timeout`), so a checking
/// stage that runs out is reported as [`UnsatProofOutcome::Inconclusive`] —
/// the honest bare `Evidence::Unsat(None)` below, same as a search timeout —
/// never as a certified `Proved`.
///
/// # Errors
///
/// Returns [`SolverError`] from the proof export, including a soundness alarm if
/// the proof core finds a model where the backend reported `unsat`.
fn drat_qf_bv_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
    progress: Option<&crate::backend::ProofProgress>,
    check_progress: Option<&crate::backend::CheckProgress>,
) -> Result<(Evidence, Vec<TrustStep>), SolverError> {
    // Already out of budget: do not even pay the bit-blast + Tseitin encoding the
    // exporter would redo before consulting the deadline.
    if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        return Ok((
            Evidence::Unsat(None),
            trust_steps(&[
                (TrustId::BitBlast, false),
                (TrustId::Tseitin, false),
                (TrustId::SatRefutation, false),
            ]),
        ));
    }
    // The checking-stage sink: forwards to `check_progress.sink` when set,
    // else a no-op. Built once and moved into whichever branch below
    // actually runs, exactly as `send` is for the search-side sink.
    let want_check_progress = check_progress.is_some();
    let check_interval = check_progress.map_or(1, |c| c.interval);
    let check_max_steps = check_progress.and_then(|c| c.max_steps);
    let mut send_check = |event: &CheckingProgress| {
        if let Some(check_progress) = check_progress {
            let _ = check_progress.sink.send(*event);
        }
    };
    let check_budget = CheckBudget {
        deadline,
        max_steps: check_max_steps,
        progress_interval: check_interval,
        progress: if want_check_progress {
            Some(&mut send_check as &mut dyn FnMut(&CheckingProgress))
        } else {
            None
        },
    };
    let outcome = match progress {
        None => export_qf_bv_unsat_proof_within_with_check_budget(
            arena,
            assertions,
            deadline,
            check_budget,
        )?,
        Some(progress) => {
            // A closed receiver must never fail, let alone abort, the search: a
            // progress report reaching nobody is not a search error.
            let mut send = |snapshot: &axeyum_cnf::ProofSearchProgress| {
                let _ = progress.sink.send(*snapshot);
            };
            export_qf_bv_unsat_proof_with_progress(
                arena,
                assertions,
                deadline,
                axeyum_cnf::DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
                progress.interval,
                &mut send,
                check_budget,
            )?
        }
    };
    Ok(match outcome {
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

fn produce_arith_dpll_evidence(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<EvidenceReport>, SolverError> {
    if !contains_arithmetic_content(arena, assertions) {
        return Ok(None);
    }
    let provenance = Provenance {
        semantics_version: SEMANTICS_VERSION,
        layers: LayerVersions::CURRENT,
        backend: "arith-dpll-exact-theory-enumeration".to_owned(),
        assertion_count: assertions.len(),
        timeout: config.timeout,
        resource_limit: config.resource_limit,
        node_budget: config.node_budget,
        cnf_variable_budget: config.cnf_variable_budget,
        cnf_clause_budget: config.cnf_clause_budget,
        prove_unsat: true,
    };
    match certify_arith_dpll_unsat(arena, assertions, config) {
        Ok(ArithDpllOutcome::Sat(model)) => Ok(Some(EvidenceReport {
            evidence: Evidence::Sat(model),
            provenance,
            trusted_steps: Vec::new(),
        })),
        Ok(ArithDpllOutcome::Unsat(refutation)) => Ok(Some(EvidenceReport {
            evidence: Evidence::UnsatArithDpll(refutation),
            provenance,
            trusted_steps: Vec::new(),
        })),
        Ok(ArithDpllOutcome::Unknown(_)) | Err(SolverError::Unsupported(_)) => Ok(None),
        Err(error) => Err(error),
    }
}

fn contains_arithmetic_content(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if matches!(arena.sort_of(term), Sort::Int | Sort::Real) {
            return true;
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    false
}

/// Node budget for the pre-solve zero-trust Alethe attempt: generous for the
/// small structural rows it exists to upgrade, small enough that a BMC-scale
/// instance never pays for speculative proof emission before its fast
/// structural certificate fires.
const PRE_SOLVE_ALETHE_MAX_NODES: usize = 2_000;

/// Whether the assertions' term DAG has at most `cap` distinct nodes (early
/// exit past the cap; O(min(dag, cap))).
fn assertion_dag_within(arena: &TermArena, assertions: &[TermId], cap: usize) -> bool {
    let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if seen.len() > cap {
            return false;
        }
        if let TermNode::App { args, .. } = arena.node(t) {
            stack.extend(args.iter().copied());
        }
    }
    true
}

/// Query-level evidence for a **conjunctive** difference-logic (`QF_IDL` /
/// `QF_RDL`) `unsat`: the negative cycle the online theory finds, exported once
/// for the whole query as the existing [`FarkasCertificate`].
///
/// Before this, a difference-logic refutation was rebuilt and
/// [`FarkasCertificate::verify`]-checked **per theory conflict** inside
/// `dl_online` and then dropped, so the front door saw a bare `unsat`. This is
/// the same certificate object `QF_LRA` already emits — no new evidence format,
/// and `Evidence::check` re-runs the same independent exact-rational verifier.
///
/// **Scope, stated honestly.** Conjunctive queries only. With Boolean structure
/// the refutation is a resolution over many theory lemmas, which a single Farkas
/// combination cannot express; that case keeps whatever the routes below produce.
/// The producer also declines any refutation that depends on the integer
/// tightening `< c ⇒ ≤ ⌈c⌉ - 1`, because the emitted atoms are the query's
/// verbatim relations (see [`crate::dl_online::conjunctive_farkas_certificate`]).
fn dl_conjunctive_farkas_report(
    arena: &mut TermArena,
    assertions: &[TermId],
    provenance: &Provenance,
) -> Option<EvidenceReport> {
    let certificate = crate::dl_online::conjunctive_farkas_certificate(arena, assertions)?;
    Some(EvidenceReport {
        evidence: Evidence::UnsatFarkas(certificate),
        provenance: Provenance {
            backend: "dl-online-negative-cycle-farkas".to_owned(),
            prove_unsat: true,
            ..provenance.clone()
        },
        trusted_steps: trust_steps(&[(TrustId::Farkas, true)]),
    })
}

/// The **correct-verdict** difference-logic fallback for queries the conjunctive
/// certificate does not cover.
///
/// Measured, and the reason this exists: on the committed 200-file `QF_RDL`
/// parity list the evidence front door decided **2** files while the solver front
/// door decided 105. `evidence_route` sends a pure-real query to `PureReal`,
/// whose lazy-SMT / Farkas engine is the *only* thing it tries — it never reaches
/// the auto dispatcher, so the difference-logic procedure that decides those
/// files in milliseconds was never run and the report came back `unknown`. A
/// correct verdict with an honest bare `unsat` strictly dominates an `unknown`.
///
/// It runs under [`crate::auto::dl_probe_budget`] — the same reservation the
/// solver dispatcher uses — so a probe that runs out of time leaves the routes
/// below it a usable slice instead of consuming the whole budget. `sat` is the
/// procedure's own model, already replayed through the ground evaluator against
/// the ORIGINAL assertions; `unsat` came from Farkas-verified negative cycles.
/// A `None`/`unknown` is a clean fall-through, leaving every route below
/// byte-identical.
///
/// **Size-gated so it never downgrades a certificate.** Small queries are left to
/// the certifying routes below (which can emit `UnsatLraDpll` /
/// `UnsatArithAletheProof` for a Boolean-structured refutation); this only takes
/// over above `PRE_SOLVE_ALETHE_MAX_NODES`, where those routes return `unknown`
/// in practice. The conjunctive certificate path
/// ([`dl_conjunctive_farkas_report`]) is unaffected by the gate — it runs at
/// every size, because it *is* a certificate.
fn dl_decided_report(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    provenance: &Provenance,
) -> Option<EvidenceReport> {
    if assertion_dag_within(arena, assertions, PRE_SOLVE_ALETHE_MAX_NODES) {
        return None;
    }
    let evidence = match crate::dl_online::try_check_qf_dl(
        arena,
        assertions,
        &crate::auto::dl_probe_budget(config),
        crate::auto::extended_dl_probe_timeout(config),
    )? {
        CheckResult::Sat(model) => Evidence::Sat(model),
        // Correct, and honestly recorded as uncertified: the Boolean-structured
        // refutation is a resolution over theory lemmas that no single Farkas
        // combination expresses (see `dl_conjunctive_farkas_report`).
        CheckResult::Unsat => Evidence::Unsat(None),
        CheckResult::Unknown(_) => return None,
    };
    Some(EvidenceReport {
        evidence,
        provenance: Provenance {
            backend: "dl-online".to_owned(),
            ..provenance.clone()
        },
        trusted_steps: Vec::new(),
    })
}

fn residue_evidence(arena: &TermArena, assertions: &[TermId]) -> Option<Evidence> {
    crate::quant_residue_cert::int_euclidean_residue_refutation(arena, assertions)
        .map(Evidence::UnsatIntEuclideanResidue)
}

fn residue_report(
    arena: &TermArena,
    assertions: &[TermId],
    provenance: &Provenance,
) -> Option<EvidenceReport> {
    Some(EvidenceReport {
        evidence: residue_evidence(arena, assertions)?,
        provenance: provenance.clone(),
        trusted_steps: Vec::new(),
    })
}

fn affine_growth_evidence(arena: &TermArena, assertions: &[TermId]) -> Option<Evidence> {
    crate::quant_affine_growth_cert::int_affine_growth_refutation(arena, assertions)
        .map(Evidence::UnsatIntAffineGrowth)
}

fn nested_xor_evidence(arena: &TermArena, assertions: &[TermId]) -> Option<Evidence> {
    crate::quant_nested_xor_cert::int_nested_xor_refutation(arena, assertions)
        .map(Evidence::UnsatIntNestedXor)
}

/// Re-decide a quantified query by e-matching, keeping the instances it used.
///
/// Top-level existentials are eliminated first, by the same
/// `eliminate_top_existentials` [`crate::auto::solve`] uses. Without that step
/// a query like `∃b. ∀x. …` has no top-level universal for the driver to
/// instantiate at all, so the whole route declined on it (`F:barber-no-such-barber`,
/// measured `unsat-uncertified`). The elimination is carried in the certificate
/// as a per-assertion binder COUNT and the checker redoes it in its own arena,
/// which is what makes the witnesses nameable there -- see
/// `quant_instance_set_cert`. On a query with no top-level existential this is
/// the identity and the route behaves exactly as before.
///
/// Unlike the other producers this one runs on the caller's `arena` rather than
/// a clone, deliberately: the skolemised assertions and the instances the driver
/// builds must live in one arena for the driver's own build-time replay to
/// resolve. `produce_evidence` holds `&mut`, so they do. Nothing that lives only
/// there reaches the certificate.
///
/// Declines unless the refutation is exactly "the skolemised assertions plus
/// checked instances", and unless every binding can be named portably.
fn quant_instance_set_certificate(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<crate::quant_instance_set_cert::QuantifierInstanceSetCertificate>, SolverError> {
    let elimination = crate::auto::eliminate_top_existentials(arena, assertions)?;
    let mut derivations = None;
    let result = crate::qinst_egraph::prove_quantified_unsat_via_egraph_with_instances(
        arena,
        &elimination.assertions,
        config,
        &mut derivations,
    )?;
    if !matches!(result, CheckResult::Unsat) {
        return Ok(None);
    }
    Ok(derivations.and_then(|derivations| {
        crate::quant_instance_set_cert::portable_certificate(
            arena,
            assertions,
            &elimination,
            &derivations,
        )
    }))
}

fn quantified_structural_unsat_evidence(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Evidence> {
    residue_evidence(arena, assertions)
        .or_else(|| affine_growth_evidence(arena, assertions))
        .or_else(|| nested_xor_evidence(arena, assertions))
        .or_else(|| {
            crate::quant_eq_partition_search::equality_partition_refutation(arena, assertions)
                .map(Evidence::UnsatEqualityPartition)
        })
}

fn affine_growth_report(
    arena: &TermArena,
    assertions: &[TermId],
    provenance: &Provenance,
) -> Option<EvidenceReport> {
    Some(EvidenceReport {
        evidence: affine_growth_evidence(arena, assertions)?,
        provenance: provenance.clone(),
        trusted_steps: Vec::new(),
    })
}

fn nested_xor_report(
    arena: &TermArena,
    assertions: &[TermId],
    provenance: &Provenance,
) -> Option<EvidenceReport> {
    Some(EvidenceReport {
        evidence: nested_xor_evidence(arena, assertions)?,
        provenance: provenance.clone(),
        trusted_steps: Vec::new(),
    })
}

fn closed_universal_counterexample_report(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    provenance: &Provenance,
) -> Result<Option<EvidenceReport>, SolverError> {
    let Some(certificate) =
        crate::quant_closed_counterexample_search::find_closed_universal_counterexample(
            arena, assertions, config,
        )?
    else {
        return Ok(None);
    };
    Ok(Some(EvidenceReport {
        evidence: Evidence::UnsatClosedUniversalCounterexample(certificate),
        provenance: provenance.clone(),
        trusted_steps: Vec::new(),
    }))
}

fn vacuous_exists_universal_counterexample_report(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    provenance: &Provenance,
) -> Result<Option<EvidenceReport>, SolverError> {
    let Some(certificate) = crate::quant_vacuous_exists_counterexample_search::find_vacuous_exists_universal_counterexample(
        arena, assertions, config,
    )? else {
        return Ok(None);
    };
    Ok(Some(EvidenceReport {
        evidence: Evidence::UnsatVacuousExistsUniversalCounterexample(certificate),
        provenance: provenance.clone(),
        trusted_steps: Vec::new(),
    }))
}

fn bv_paired_existential_transfer_report(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    provenance: &Provenance,
) -> Result<Option<EvidenceReport>, SolverError> {
    let Some(certificate) =
        crate::quant_bv_paired_exists_search::find_bv_paired_existential_transfer(
            arena, assertions, config,
        )?
    else {
        return Ok(None);
    };
    Ok(Some(EvidenceReport {
        evidence: Evidence::UnsatBvPairedExistentialTransfer(certificate),
        provenance: provenance.clone(),
        trusted_steps: Vec::new(),
    }))
}

fn negated_existential_witness_report(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    provenance: &Provenance,
) -> Result<Option<EvidenceReport>, SolverError> {
    let Some(certificate) = crate::quant_negated_exists_search::find_negated_existential_witness(
        arena, assertions, config,
    )?
    else {
        return Ok(None);
    };
    Ok(Some(EvidenceReport {
        evidence: Evidence::UnsatNegatedExistentialWitness(certificate),
        provenance: provenance.clone(),
        trusted_steps: Vec::new(),
    }))
}

fn bv_alternation_counterexample_report(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    provenance: &Provenance,
) -> Result<Option<EvidenceReport>, SolverError> {
    let Some(certificate) = crate::quant_bv_alternation_search::find_bv_alternation_counterexample(
        arena, assertions, config,
    )?
    else {
        return Ok(None);
    };
    Ok(Some(EvidenceReport {
        evidence: Evidence::UnsatBvAlternationCounterexample(certificate),
        provenance: provenance.clone(),
        trusted_steps: Vec::new(),
    }))
}

fn bv_conjunctive_universal_instance_report(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    provenance: &Provenance,
) -> Result<Option<EvidenceReport>, SolverError> {
    let Some(certificate) =
        crate::quant_bv_conjunctive_search::find_bv_conjunctive_universal_instance(
            arena, assertions, config,
        )?
    else {
        return Ok(None);
    };
    Ok(Some(EvidenceReport {
        evidence: Evidence::UnsatBvConjunctiveUniversalInstance(certificate),
        provenance: provenance.clone(),
        trusted_steps: Vec::new(),
    }))
}

fn bv_positive_universal_instance_set_report(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    provenance: &Provenance,
) -> Result<Option<EvidenceReport>, SolverError> {
    let Some(certificate) = crate::quant_bool_model_sat::find_bv_positive_universal_instance_set(
        arena, assertions, config,
    )?
    else {
        return Ok(None);
    };
    Ok(Some(EvidenceReport {
        evidence: Evidence::UnsatBvPositiveUniversalInstanceSet(certificate),
        provenance: provenance.clone(),
        trusted_steps: Vec::new(),
    }))
}

fn equality_partition_report(
    arena: &TermArena,
    assertions: &[TermId],
    provenance: &Provenance,
) -> Option<EvidenceReport> {
    Some(EvidenceReport {
        evidence: Evidence::UnsatEqualityPartition(
            crate::quant_eq_partition_search::equality_partition_refutation(arena, assertions)?,
        ),
        provenance: provenance.clone(),
        trusted_steps: Vec::new(),
    })
}

fn quantified_counterexample_cover_report(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    provenance: &Provenance,
) -> Result<Option<EvidenceReport>, SolverError> {
    let Some(certificate) =
        crate::quant_counterexample_cover::quantified_counterexample_cover_refutation(
            arena, assertions, config,
        )?
    else {
        return Ok(None);
    };
    Ok(Some(EvidenceReport {
        evidence: Evidence::UnsatQuantifiedCounterexampleCover(certificate),
        provenance: provenance.clone(),
        trusted_steps: Vec::new(),
    }))
}

fn direct_pre_solve_structural_report(
    arena: &mut TermArena,
    assertions: &[TermId],
    provenance: &Provenance,
) -> Option<EvidenceReport> {
    if let Some(cert) = crate::term_identity::term_identity_refutation(arena, assertions) {
        return Some(EvidenceReport {
            evidence: Evidence::UnsatTermIdentity(cert),
            provenance: provenance.clone(),
            trusted_steps: Vec::new(),
        });
    }
    if let Some(cert) = crate::bool_simplify::bool_simplification_refutation(arena, assertions) {
        return Some(EvidenceReport {
            evidence: Evidence::UnsatBoolSimplification(cert),
            provenance: provenance.clone(),
            trusted_steps: Vec::new(),
        });
    }
    if let Some(cert) = crate::ufbv_finite::bool_uf_exhaustive_refutation(arena, assertions) {
        return Some(EvidenceReport {
            evidence: Evidence::UnsatBoolUfExhaustive(cert),
            provenance: provenance.clone(),
            trusted_steps: Vec::new(),
        });
    }
    // Prefer the ZERO-trust Alethe refutations over the structural certificates
    // below whenever the same instance supports both: an Alethe proof is
    // externally re-checkable (`check_alethe` / Carcara) — strictly stronger
    // evidence for the Lean-parity ledger. The structural pre-solve hooks had
    // shadowed these routes since they landed (e7bfed4c and successors),
    // silently downgrading `produce_evidence`'s certificate strength on EUF,
    // Ackermann-UFBV, and array read-consistency rows. Each emitter
    // self-validates and declines outside its fragment — but the attempts are
    // not free on LARGE instances (the elimination/Ackermann emitters expand
    // the query), so this pre-solve upgrade is size-gated: big instances (e.g.
    // the FIFO BC04 BMC rows) keep their fast structural certificates here,
    // and still get an Alethe upgrade attempt on the post-solve `Unsat` path.
    if assertion_dag_within(arena, assertions, PRE_SOLVE_ALETHE_MAX_NODES) {
        if let Some(proof) = zero_trust_alethe_certificate(arena, assertions) {
            return Some(EvidenceReport {
                evidence: Evidence::UnsatAletheProof(proof),
                provenance: provenance.clone(),
                trusted_steps: Vec::new(),
            });
        }
        // The mixed UF+linear-arithmetic zero-trust emitter (congruence-then-
        // arithmetic conflicts, e.g. `f(x)=1 ∧ f(y)=2 ∧ x=y`) — otherwise the
        // structural `uf_arith_congruence` certificate below shadows it.
        if let Some(proof) = uflia_alethe_certificate(arena, assertions) {
            return Some(EvidenceReport {
                evidence: Evidence::UnsatArithAletheProof(proof),
                provenance: provenance.clone(),
                trusted_steps: Vec::new(),
            });
        }
    }
    if let Some(cert) = crate::bool_euf::bool_euf_exhaustive_refutation(arena, assertions) {
        return Some(EvidenceReport {
            evidence: Evidence::UnsatBoolEufExhaustive(cert),
            provenance: provenance.clone(),
            trusted_steps: Vec::new(),
        });
    }
    if let Some(cert) = crate::bool_euf::bool_euf_online_refutation(arena, assertions) {
        return Some(EvidenceReport {
            evidence: Evidence::UnsatBoolEufOnline(cert),
            provenance: provenance.clone(),
            trusted_steps: Vec::new(),
        });
    }
    if let Some(cert) = crate::uf_arith::uf_arith_congruence_refutation(arena, assertions) {
        return Some(EvidenceReport {
            evidence: Evidence::UnsatUfArithCongruence(cert),
            provenance: provenance.clone(),
            trusted_steps: Vec::new(),
        });
    }
    if let Some(cert) =
        crate::datatype_acyclicity::datatype_structural_refutation(arena, assertions)
    {
        return Some(EvidenceReport {
            evidence: Evidence::UnsatDatatypeStructural(cert),
            provenance: provenance.clone(),
            trusted_steps: Vec::new(),
        });
    }
    if let Some(cert) =
        crate::bv_forall_nonconstant::bv_forall_nonconstant_refutation(arena, assertions)
    {
        return Some(EvidenceReport {
            evidence: Evidence::UnsatBvForallNonconstant(cert),
            provenance: provenance.clone(),
            trusted_steps: Vec::new(),
        });
    }
    if let Some(cert) = crate::bv_uf_local::bv_uf_local_refutation(arena, assertions) {
        return Some(EvidenceReport {
            evidence: Evidence::UnsatBvUfLocal(cert),
            provenance: provenance.clone(),
            trusted_steps: Vec::new(),
        });
    }
    if let Some(cert) = crate::set_cardinality::set_cardinality_refutation(arena, assertions) {
        return Some(EvidenceReport {
            evidence: Evidence::UnsatSetCardinality(cert),
            provenance: provenance.clone(),
            trusted_steps: Vec::new(),
        });
    }
    if let Some(cert) = crate::bv_defined_enum::bv_defined_enum_refutation(arena, assertions) {
        return Some(EvidenceReport {
            evidence: Evidence::UnsatBvDefinedEnum(cert),
            provenance: provenance.clone(),
            trusted_steps: Vec::new(),
        });
    }
    direct_pre_solve_array_report(arena, assertions, provenance)
}

fn direct_pre_solve_array_report(
    arena: &TermArena,
    assertions: &[TermId],
    provenance: &Provenance,
) -> Option<EvidenceReport> {
    if let Some(cert) = crate::abv::const_array_default_mismatch_refutation(arena, assertions) {
        return Some(EvidenceReport {
            evidence: Evidence::UnsatConstArrayDefaultMismatch(cert),
            provenance: provenance.clone(),
            trusted_steps: Vec::new(),
        });
    }
    if let Some(cert) = crate::abv::store_chain_readback_refutation(arena, assertions) {
        return Some(EvidenceReport {
            evidence: Evidence::UnsatStoreChainReadback(cert),
            provenance: provenance.clone(),
            trusted_steps: Vec::new(),
        });
    }
    if let Some(cert) = crate::abv::cross_store_array_disequality_refutation(arena, assertions) {
        return Some(EvidenceReport {
            evidence: Evidence::UnsatCrossStoreArrayDisequality(cert),
            provenance: provenance.clone(),
            trusted_steps: Vec::new(),
        });
    }
    small_pre_solve_array_axiom_refutation(arena, assertions).map(|cert| EvidenceReport {
        evidence: Evidence::UnsatArrayAxiom(cert),
        provenance: provenance.clone(),
        trusted_steps: Vec::new(),
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

/// Produces a self-checking degree-2 **sum-of-squares / PSD** `unsat` certificate
/// (ADR-0039) for a conjunction whose first STRICT quadratic inequality atom is
/// globally one-signed: `p < 0` refuted by `M ⪰ 0` (⇒ `p ≥ 0 ∀x`), or `p > 0` by
/// `−M ⪰ 0` (⇒ `p ≤ 0 ∀x`). The carried [`SosCertificate`] is fully
/// self-contained — [`Evidence::check`] re-validates it via
/// [`SosCertificate::verify`] (an exact-rational `LDLᵀ` reconstruction), independent
/// of the arena.
///
/// Returns `Ok(Some(report))` when such a certificate exists, else `Ok(None)`
/// (decline — no wrong verdict is ever produced). This is an *additive*,
/// exact-arithmetic NRA `unsat` certificate; it never produces `sat`.
///
/// # Errors
///
/// Returns [`SolverError`] only to match the producer signatures; this path does
/// not currently fail (the result is always `Ok`).
#[allow(
    clippy::unnecessary_wraps,
    reason = "signature matches the other evidence producers' Result contract"
)]
pub fn produce_nra_sos_evidence(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<EvidenceReport>, SolverError> {
    let Some(cert) = nra_real_root::sos_refute_with_certificate(arena, assertions) else {
        return Ok(None);
    };
    // Best-effort Lean-backed evidence (ADR-0041): when the SOS→Lean reconstruction
    // covers this query's shape, carry the kernel-checked module. `None` keeps the
    // (still self-checked) certificate evidence for shapes the reconstruction slice
    // does not yet cover — never an error.
    let lean_module = crate::reconstruct::reconstruct_sos_to_lean_module(arena, assertions).ok();
    let provenance = Provenance {
        semantics_version: SEMANTICS_VERSION,
        layers: LayerVersions::CURRENT,
        backend: "nra-sos-psd-certificate".to_owned(),
        assertion_count: assertions.len(),
        timeout: None,
        resource_limit: None,
        node_budget: None,
        cnf_variable_budget: None,
        cnf_clause_budget: None,
        prove_unsat: true,
    };
    Ok(Some(EvidenceReport {
        evidence: Evidence::UnsatSos {
            certificate: cert,
            lean_module,
        },
        provenance,
        // Exact, self-checked SOS/PSD certificate — certified this run.
        trusted_steps: trust_steps(&[(TrustId::Sos, true)]),
    }))
}

/// Produces a checked NRA refutation for strict negative sums of syntactic even
/// powers, such as `x^4 < 0` or `(x-1)^4 + (y-2)^4 + 1 < 0`.
///
/// # Errors
///
/// Returns [`SolverError`] only to match the other evidence producers' `Result`
/// contract; this path does not currently fail (the result is always `Ok`).
#[allow(
    clippy::unnecessary_wraps,
    reason = "signature matches the other evidence producers' Result contract"
)]
pub fn produce_nra_even_power_evidence(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<EvidenceReport>, SolverError> {
    let Some(cert) = crate::nra_even_power::nra_even_power_refutation(arena, assertions) else {
        return Ok(None);
    };
    let provenance = Provenance {
        semantics_version: SEMANTICS_VERSION,
        layers: LayerVersions::CURRENT,
        backend: "nra-even-power-certificate".to_owned(),
        assertion_count: assertions.len(),
        timeout: None,
        resource_limit: None,
        node_budget: None,
        cnf_variable_budget: None,
        cnf_clause_budget: None,
        prove_unsat: true,
    };
    Ok(Some(EvidenceReport {
        evidence: Evidence::UnsatNraEvenPower(cert),
        provenance,
        trusted_steps: Vec::new(),
    }))
}

/// Produce source-bound evidence for a monomial-bound refutation.
pub fn produce_monomial_bound_evidence(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<EvidenceReport> {
    let certificate = crate::nra_monomial_bound_cert::monomial_bound_refutation(arena, assertions)?;
    Some(EvidenceReport {
        evidence: Evidence::UnsatMonomialBound(certificate),
        provenance: Provenance {
            semantics_version: SEMANTICS_VERSION,
            layers: LayerVersions::CURRENT,
            backend: "nra-monomial-bound-certificate".to_owned(),
            assertion_count: assertions.len(),
            timeout: None,
            resource_limit: None,
            node_budget: None,
            cnf_variable_budget: None,
            cnf_clause_budget: None,
            prove_unsat: true,
        },
        trusted_steps: Vec::new(),
    })
}

/// Produce source-bound evidence for a degree-2 Positivstellensatz refutation.
pub fn produce_real_product_evidence(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<EvidenceReport> {
    let certificate = crate::nra_product_cert::real_product_refutation(arena, assertions)?;
    Some(EvidenceReport {
        evidence: Evidence::UnsatRealProduct(certificate),
        provenance: Provenance {
            semantics_version: SEMANTICS_VERSION,
            layers: LayerVersions::CURRENT,
            backend: "nra-product-positivstellensatz-certificate".to_owned(),
            assertion_count: assertions.len(),
            timeout: None,
            resource_limit: None,
            node_budget: None,
            cnf_variable_budget: None,
            cnf_clause_budget: None,
            prove_unsat: true,
        },
        trusted_steps: Vec::new(),
    })
}

/// Produce source-bound evidence for a multi-term Handelman / Positivstellensatz
/// refutation.
///
/// Declines (`None`) for anything purely linear -- a linear refutation is a Farkas
/// refutation and the linear route already carries one -- and for any nonlinear
/// query whose combination the bounded search does not find.
pub fn produce_handelman_evidence(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<EvidenceReport> {
    let certificate = crate::nra_handelman_cert::handelman_refutation(arena, assertions)?;
    Some(EvidenceReport {
        evidence: Evidence::UnsatRealHandelman(certificate),
        provenance: Provenance {
            semantics_version: SEMANTICS_VERSION,
            layers: LayerVersions::CURRENT,
            backend: "nra-handelman-positivstellensatz-certificate".to_owned(),
            assertion_count: assertions.len(),
            timeout: None,
            resource_limit: None,
            node_budget: None,
            cnf_variable_budget: None,
            cnf_clause_budget: None,
            prove_unsat: true,
        },
        trusted_steps: Vec::new(),
    })
}

/// Produce source-bound evidence for a real monomial-divisibility refutation.
pub fn produce_real_zero_product_evidence(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<EvidenceReport> {
    let certificate =
        crate::nra_zero_product_cert::real_zero_product_refutation(arena, assertions)?;
    Some(EvidenceReport {
        evidence: Evidence::UnsatRealZeroProduct(certificate),
        provenance: Provenance {
            semantics_version: SEMANTICS_VERSION,
            layers: LayerVersions::CURRENT,
            backend: "nra-zero-product-certificate".to_owned(),
            assertion_count: assertions.len(),
            timeout: None,
            resource_limit: None,
            node_budget: None,
            cnf_variable_budget: None,
            cnf_clause_budget: None,
            prove_unsat: true,
        },
        trusted_steps: Vec::new(),
    })
}

/// Produce source-bound evidence for a single-variable integer polynomial
/// equality refuted by a non-square discriminant, non-integral rational roots,
/// or rational-root exhaustion.
///
/// Runs *after* [`produce_int_quadratic_negative_discriminant_evidence`] and
/// declines on the negative-discriminant shape, so one query never has two
/// competing artifacts to keep in agreement.
pub fn produce_int_univariate_poly_evidence(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<EvidenceReport> {
    let certificate = crate::nia_univariate_cert::int_univariate_refutation(arena, assertions)?;
    Some(EvidenceReport {
        evidence: Evidence::UnsatIntUnivariatePoly(certificate),
        provenance: Provenance {
            semantics_version: SEMANTICS_VERSION,
            layers: LayerVersions::CURRENT,
            backend: "nia-univariate-polynomial-certificate".to_owned(),
            assertion_count: assertions.len(),
            timeout: None,
            resource_limit: None,
            node_budget: None,
            cnf_variable_budget: None,
            cnf_clause_budget: None,
            prove_unsat: true,
        },
        trusted_steps: Vec::new(),
    })
}

/// Produce source-bound evidence for the negative-discriminant subset of
/// single-variable integer quadratic equalities.
pub fn produce_int_quadratic_negative_discriminant_evidence(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<EvidenceReport> {
    let certificate =
        crate::nia_square::int_quadratic_negative_discriminant_refutation(arena, assertions)?;
    Some(EvidenceReport {
        evidence: Evidence::UnsatIntQuadraticNegativeDiscriminant(certificate),
        provenance: Provenance {
            semantics_version: SEMANTICS_VERSION,
            layers: LayerVersions::CURRENT,
            backend: "nia-quadratic-negative-discriminant-certificate".to_owned(),
            assertion_count: assertions.len(),
            timeout: None,
            resource_limit: None,
            node_budget: None,
            cnf_variable_budget: None,
            cnf_clause_budget: None,
            prove_unsat: true,
        },
        trusted_steps: Vec::new(),
    })
}

/// Attaches a self-checking, Lean-backed integer-infeasibility certificate to a
/// system of integer equalities that the Diophantine decision proves `unsat`
/// (ADR-0043). The carried [`DiophantineCertificate`] is fully self-contained:
/// [`Evidence::check`] re-validates it via [`check_diophantine_certificate`] (an
/// integer-Farkas recombination re-derived from the originals, independent of the
/// producer), and — when [`crate::int_reconstruct::reconstruct_diophantine_to_lean_module`]
/// covers the query shape — ALSO re-derives the kernel-checked Lean module.
///
/// Returns `Ok(None)` when the system is not a Diophantine-refutable integer
/// infeasibility (never a wrong `unsat`).
///
/// # Errors
///
/// Returns [`SolverError`] only to match the other evidence producers' `Result`
/// contract; this path does not currently fail (the result is always `Ok`).
#[allow(
    clippy::unnecessary_wraps,
    reason = "signature matches the other evidence producers' Result contract"
)]
pub fn produce_diophantine_evidence(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<EvidenceReport>, SolverError> {
    if !contains_arithmetic_content(arena, assertions) {
        return Ok(None);
    }
    let Some((equalities, certificate)) =
        prove_lia_unsat_by_diophantine_certified(arena, assertions)
    else {
        return Ok(None);
    };
    // Best-effort Lean-backed evidence (ADR-0043): when the Diophantine→Lean
    // reconstruction covers this query's shape, carry the kernel-checked module.
    // `None` keeps the (still self-checked) certificate evidence for shapes the
    // reconstruction slice does not yet cover — never an error.
    let lean_module =
        crate::int_reconstruct::reconstruct_diophantine_to_lean_module(arena, assertions).ok();
    let provenance = Provenance {
        semantics_version: SEMANTICS_VERSION,
        layers: LayerVersions::CURRENT,
        backend: "lia-diophantine-certificate".to_owned(),
        assertion_count: assertions.len(),
        timeout: None,
        resource_limit: None,
        node_budget: None,
        cnf_variable_budget: None,
        cnf_clause_budget: None,
        prove_unsat: true,
    };
    Ok(Some(EvidenceReport {
        evidence: Evidence::UnsatDiophantine {
            equalities,
            certificate,
            lean_module,
        },
        provenance,
        // Exact, self-checked integer-Farkas certificate — certified this run.
        trusted_steps: trust_steps(&[(TrustId::Diophantine, true)]),
    }))
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
#[allow(clippy::too_many_lines)]
pub fn produce_evidence(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<EvidenceReport, SolverError> {
    let evidence_deadline = config
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
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
    // A CONJUNCTIVE difference-logic refutation is a negative cycle, i.e. a Farkas
    // combination with unit multipliers over the query's own relations. It is
    // polynomial to find and independently re-checkable, so it runs ahead of the
    // route split: `QF_RDL` would otherwise reach `PureReal` (whose DPLL(T)/Farkas
    // engine times out on the very instances difference logic decides in
    // milliseconds) and `QF_IDL` would reach the `Other` chain and land as a bare
    // `unsat`. It declines — on the first non-numeric sort, so a `QF_BV` query pays
    // two loop iterations — for anything outside pure difference logic, anything
    // with Boolean structure, and any refutation needing the integer tightening.
    if let Some(report) = dl_conjunctive_farkas_report(arena, assertions, &provenance) {
        return Ok(report);
    }
    // Above the certifying routes' practical size, the difference-logic DECISION
    // itself is what the front door is missing (see `dl_decided_report`): an
    // honest bare `unsat` beats the `unknown` a timed-out certificate attempt
    // returns. Small queries skip this and keep their certificate chain.
    if let Some(report) = dl_decided_report(arena, assertions, config, &provenance) {
        return Ok(report);
    }
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
            if let Some(report) = direct_pre_solve_structural_report(arena, assertions, &provenance)
            {
                return Ok(report);
            }
            // Prefer the self-checked, Lean-backed degree-2 SOS certificate when the
            // query is an SOS-decided `unsat` (ADR-0039/0041): it is re-checkable two
            // independent ways (exact-rational LDLᵀ + kernel-checked Lean), stronger
            // than the NRA abstraction's bare `unsat`. Declines (`None`) on anything
            // it does not decide, falling through to the linear / NRA route.
            if let Some(report) = produce_nra_sos_evidence(arena, assertions)? {
                return Ok(report);
            }
            if let Some(report) = produce_nra_even_power_evidence(arena, assertions)? {
                return Ok(report);
            }
            // Monomial divisibility. Must sit here, INSIDE the `PureReal` arm and
            // ahead of `produce_nra_evidence` below: that call returns a bare
            // `unsat` for anything the NRA abstraction decides, so a hook placed
            // after the `match` is unreachable for exactly the queries this
            // certifies. Placed after the `match` first, and it never fired on
            // the two corpus files it was written for.
            if let Some(report) = produce_real_zero_product_evidence(arena, assertions) {
                return Ok(report);
            }
            if let Some(report) = produce_real_product_evidence(arena, assertions) {
                return Ok(report);
            }
            if let Some(report) = produce_monomial_bound_evidence(arena, assertions) {
                return Ok(report);
            }
            // The multi-term Handelman combination: the most general of the
            // certifying `QF_NRA` routes, so it runs last of them and only after
            // the single-product shapes above have declined. Like them it must
            // sit INSIDE this arm -- `produce_nra_evidence` below answers these
            // queries with a bare `unsat`, so a hook after the `match` never
            // fires for the files it was written for.
            if let Some(report) = produce_handelman_evidence(arena, assertions) {
                return Ok(report);
            }
            match produce_lra_dpll_evidence(arena, assertions, config) {
                Ok(report) => return Ok(report),
                Err(SolverError::Unsupported(msg))
                    if msg.contains("nonlinear") || msg.contains("non-linear") =>
                {
                    match produce_nra_evidence(arena, assertions, config) {
                        Ok(report) => return Ok(report),
                        Err(SolverError::Unsupported(_)) => {}
                        Err(error) => return Err(error),
                    }
                }
                Err(SolverError::Unsupported(_)) => {}
                Err(error) => return Err(error),
            }
        }
        EvidenceRoute::Other => {}
    }

    // Everything else supported: decide with the unified engine. `sat` is
    // replay-certified; `unsat` over a BV-reducible fragment (arrays/UF/datatypes)
    // now carries a re-checkable DRAT certificate of the reduced CNF (clausal
    // layer, modulo the trusted reduction); fragments without a reduction-to-BV
    // certificate (e.g. integers/real/nonlinear) still record a bare `unsat`.
    // Prefer the self-checking, Lean-backed integer-Farkas (Diophantine) certificate
    // for an integer-systems `unsat` (ADR-0042/0043): unlike the `lia_generic` Alethe
    // route (a Carcara hole for integer systems), it is independently checkable in-tree
    // AND reconstructs to a real-`lean`-checked proof. Declines (`None`) for
    // non-integer-equality-systems, falling through to the unified engine below.
    if let Some(report) = produce_diophantine_evidence(arena, assertions)? {
        return Ok(report);
    }
    if let Some(report) = produce_int_quadratic_negative_discriminant_evidence(arena, assertions) {
        return Ok(report);
    }
    if let Some(report) = produce_int_univariate_poly_evidence(arena, assertions) {
        return Ok(report);
    }
    if let Some(report) = residue_report(arena, assertions, &provenance) {
        return Ok(report);
    }
    if let Some(report) = affine_growth_report(arena, assertions, &provenance) {
        return Ok(report);
    }
    if let Some(report) = nested_xor_report(arena, assertions, &provenance) {
        return Ok(report);
    }
    if let Some(report) =
        closed_universal_counterexample_report(arena, assertions, config, &provenance)?
    {
        return Ok(report);
    }
    if let Some(report) =
        vacuous_exists_universal_counterexample_report(arena, assertions, config, &provenance)?
    {
        return Ok(report);
    }
    if let Some(report) =
        bv_paired_existential_transfer_report(arena, assertions, config, &provenance)?
    {
        return Ok(report);
    }
    if let Some(report) =
        negated_existential_witness_report(arena, assertions, config, &provenance)?
    {
        return Ok(report);
    }
    if let Some(report) =
        bv_alternation_counterexample_report(arena, assertions, config, &provenance)?
    {
        return Ok(report);
    }
    if let Some(report) =
        bv_conjunctive_universal_instance_report(arena, assertions, config, &provenance)?
    {
        return Ok(report);
    }
    if let Some(report) =
        bv_positive_universal_instance_set_report(arena, assertions, config, &provenance)?
    {
        return Ok(report);
    }
    if let Some(report) = equality_partition_report(arena, assertions, &provenance) {
        return Ok(report);
    }
    if let Some(report) =
        quantified_counterexample_cover_report(arena, assertions, config, &provenance)?
    {
        return Ok(report);
    }
    if let Some(report) = direct_pre_solve_structural_report(arena, assertions, &provenance) {
        return Ok(report);
    }
    if let Some(report) = uflia_alethe_evidence_report(arena, assertions, &provenance) {
        return Ok(report);
    }
    // Prefer the pure LIA/LRA `lia_generic`/`la_generic` Alethe proof over the
    // arith-DPLL lemma refutation when the instance supports both: the Alethe
    // proof object is the Lean-parity ladder (re-checked by the arithmetic-aware
    // checker; the Farkas reduction CERTIFIED), whereas the DPLL refutation is a
    // structural lemma certificate. The arith-DPLL route (d3b0d2e1) had shadowed
    // this, downgrading plain QF_LIA evidence. Size-gated like the other
    // pre-solve proof attempts; larger instances keep the cheaper DPLL cert and
    // still get the Alethe attempt on the post-solve `Unsat` path.
    if assertion_dag_within(arena, assertions, PRE_SOLVE_ALETHE_MAX_NODES)
        && let Some(proof) = arith_alethe_certificate(arena, assertions)
    {
        return Ok(EvidenceReport {
            evidence: Evidence::UnsatArithAletheProof(proof),
            provenance,
            trusted_steps: trust_steps(&[(TrustId::Farkas, true)]),
        });
    }
    if let Some(report) = produce_arith_dpll_evidence(arena, assertions, config)? {
        return Ok(report);
    }
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
            } else if let Some(proof) = uflia_alethe_certificate(arena, assertions) {
                // A MIXED arithmetic-sorted UF + linear-arith `unsat` (QF_UFLIA /
                // QF_UFLRA), e.g. `f(x)=1 ∧ f(y)=2 ∧ x=y` (f:Int→Int): the
                // congruence-then-arithmetic refutation derives the functional-
                // consistency conflict by `eq_congruent` (the congruence half) and
                // the residual contradiction by `lia_generic`/`la_generic` (the
                // arithmetic half), so the proof carries ZERO trust holes. Ordered
                // AFTER `zero_trust_alethe_certificate` (so pure QF_UFBV keeps its
                // BV cert — `prove_qf_uflia_unsat_alethe` declines BV-sorted UF) and
                // BEFORE the pure LIA/LRA `arith_alethe_certificate` (whose emitters
                // decline any UF application, so they never reach this mixed case).
                (Evidence::UnsatArithAletheProof(proof), Vec::new())
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
            } else if let Some((proof, universal)) =
                guarded_quant_alethe_certificate(arena, assertions)
            {
                // A finite-expansion guarded-`Int` universal (e.g.
                // `∀x:Int. (0<=x<=2) => x>=5`): the `forall_inst_guarded` + `lia_generic`
                // refutation re-checks each instantiation step's substitution AND
                // concrete guard truth, plus the `lia_generic` ground refutation, so
                // the quantifier-instantiation reduction is CERTIFIED. Ordered AFTER
                // the ground certs (which all decline on a quantifier) and the bare
                // fallback so a quantifier-free query is never affected. This is the
                // first quantified-`unsat` evidence with a transferable certificate.
                (
                    Evidence::UnsatGuardedQuantAletheProof { proof, universal },
                    trust_steps(&[(TrustId::Farkas, true)]),
                )
            } else if let Some((proof, universal)) =
                guarded_quant_uf_alethe_certificate(arena, assertions)
            {
                // A finite-expansion guarded-`Int` universal whose body uses an
                // uninterpreted function (e.g. `∀x:Int. (0<=x<=1) => f(x)=0` with
                // `f(0)=1`): the `forall_inst_guarded` + `eq_transitive` (defining-eq
                // bridge) + `lia_generic` refutation re-checks each instantiation's
                // substitution AND concrete guard truth, the bridge to the Ackermann
                // abstraction, and the pure-LIA residual — so the quantifier-
                // instantiation reduction is CERTIFIED. Ordered AFTER the pure-LIA
                // finite-`∀` cert (whose emitter declines a UF body) and the ground
                // certs, BEFORE the bare fallback. Reuses the same
                // `Evidence::UnsatGuardedQuantAletheProof` variant: its combined
                // checker already validates all three rule families.
                (
                    Evidence::UnsatGuardedQuantAletheProof { proof, universal },
                    trust_steps(&[(TrustId::Farkas, true)]),
                )
            } else if let Some((proof, steps)) = bv2nat_bound_certificate(arena, assertions) {
                // A `bv2nat`-bound contradiction (e.g. `bv2nat(x) >= 16` for a 4-bit
                // `x`): the exact integer refuters reject a raw `bv2nat(b)` subterm,
                // so this was a bare `Unsat(None)`. Abstract each `bv2nat(b)` to a
                // fresh `Int` with its trusted range axiom `0 <= n <= 2^W-1` and emit
                // a `lia_generic` cert over the pure-LIA abstraction: the refutation
                // is re-derived (Farkas certified), only the range axiom is trusted
                // (`IntBlast`). Ordered AFTER the arithmetic certs (which decline a
                // raw `bv2nat` subterm) and BEFORE the bare fallback, so it never
                // shadows the zero-trust certs and a `bv2nat`-free query is untouched.
                (Evidence::UnsatArithAletheProof(proof), steps)
            } else if let Some(finite) = finite_domain_enum_evidence(arena, assertions)? {
                finite
            } else if let Some(direct) = direct_structural_unsat_evidence(arena, assertions) {
                direct
            } else if let Some(bounded) = bounded_int_blast_evidence(arena, assertions)? {
                bounded
            } else if let Some(certificate) =
                quant_instance_set_certificate(arena, assertions, config)?
            {
                // LAST among the certifying arms, deliberately. This re-runs
                // e-matching and describes the refutation only as "assertions
                // plus checked instances", which is weaker and more generic than
                // every Alethe certificate above it. Placed earlier it SHADOWED
                // them: measured, it displaced the guarded-quantifier UF Alethe
                // cert in four `evidence_finite_quant_uf_cert` tests and one in
                // `evidence`. Its job is to upgrade what used to be a bare
                // `Unsat(None)`, never to displace a stronger certificate.
                (Evidence::UnsatQuantInstanceSet(certificate), Vec::new())
            } else if config.timeout.is_some() {
                // The remaining fallback is an optional reduced-CNF DRAT export
                // for BV-reducible theories. It can spend substantial time outside
                // the main solver path (lowering, DRAT/LRAT checking/elaboration)
                // and therefore used to overrun evidence audits after `solve` had
                // already returned a sound `unsat`. Under an explicit wall-clock
                // evidence budget, keep the front door timely: return the decided
                // bare `unsat` and let unbudgeted/offline callers request the
                // reduction proof path.
                (Evidence::Unsat(None), Vec::new())
            } else {
                let (cert, steps) =
                    reduction_unsat_certificate(arena, assertions, evidence_deadline);
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

/// The **string-capable** evidence front door: produce a self-checking
/// [`EvidenceReport`] for an SMT-LIB *text* script, routing string queries
/// through the same word-level / online CDCL(T) decision the text solver
/// ([`crate::solve_smtlib`]) uses.
///
/// # Why a text entry point exists (soundness — task #63)
///
/// [`produce_evidence`] takes a `TermArena` + `assertions`, but an *unbounded*
/// string query cannot be represented faithfully at that layer:
///
/// - the term IR has no `str.in_re`/`str.replace`/`str.contains` operators — those
///   live only in the bounded packed-BV *encoding* or in the parser's word /
///   membership / length **side channels** (built from the parse tree, not the
///   arena), and
/// - a *word-only-fallback* script (the bounded encoder declined it wholesale)
///   has an **empty** flat assertion view, so `produce_evidence(arena, &[])` would
///   trivially — and *wrongly* — report `sat` for an `unsat` word problem.
///
/// Feeding those flat/bounded assertions to the arena front door produced
/// `certified`/`checked` **wrong verdicts** (the `QF_S`/`QF_SLIA` P0 the #62 dominance
/// audit caught: a spurious bounded `sat` for an `unsat` word/regex problem, and a
/// bounded `unsat` for a `sat` membership problem — each passing `Evidence::check`
/// against the *same* bounded/empty view). This front door decides the script with
/// [`crate::solve_smtlib`] — whose `sat` is **Seq-level** replay-checked and whose
/// `unsat` is a certified word-clash / regex-emptiness / concat-emptiness / length
/// conflict — and wraps that already-sound verdict. It never fabricates a bounded
/// model with `checked = true`.
///
/// Non-string scripts delegate to [`produce_evidence`] over the flat assertion
/// view, so every existing rich-certificate route (DRAT, Farkas, Diophantine,
/// Alethe, …) is preserved byte-for-byte.
///
/// # Checking the result
///
/// This entry point **drops the arena it parsed**, so a consumer holding only the
/// report has no subject to re-check it against. Use
/// [`produce_evidence_smtlib_with_script`] when you intend to re-validate: it
/// hands back the same report together with the [`axeyum_smtlib::Script`] it was
/// produced from, and its [`EvidenceWithScript::check_outcome`] knows when that
/// view is *not* a faithful subject. Re-parsing the text instead makes
/// correctness depend on two parses agreeing on `SymbolId` assignment (ADR-0384).
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text, or any [`SolverError`]
/// from the chosen engine.
pub fn produce_evidence_smtlib(
    input: &str,
    config: &SolverConfig,
) -> Result<EvidenceReport, SolverError> {
    Ok(produce_evidence_smtlib_with_script(input, config)?.report)
}

/// A produced [`EvidenceReport`] together with the parsed
/// [`Script`](axeyum_smtlib::Script) it came from — the checking subject, kept
/// instead of discarded (ADR-0384).
///
/// [`produce_evidence_smtlib`] parses internally and returns only the report, so
/// a consumer that wants to run [`Evidence::check_outcome`] on its own result has
/// to re-parse the text and hope the second parse assigns the same
/// [`SymbolId`](axeyum_ir::SymbolId)s — correctness resting on parse determinism.
/// This type removes that step: [`EvidenceWithScript::check_outcome`] re-checks
/// against the *same* arena the evidence was produced against.
#[derive(Debug)]
pub struct EvidenceWithScript {
    /// The evidence and its versioned provenance.
    pub report: EvidenceReport,
    /// The parsed script the report was produced from. Its
    /// [`arena`](axeyum_smtlib::Script::arena) and
    /// [`assertions`](axeyum_smtlib::Script::assertions) are the flat view the
    /// arena front door decided (for a non-string script, the evidence's
    /// checking subject); the string side channels live on the same object.
    ///
    /// For a non-string script the arena has been *extended* by evidence
    /// production (definitions, Ackermann/array-elimination terms); the recorded
    /// assertion `TermId`s stay valid.
    pub script: axeyum_smtlib::Script,
    /// Whether `script.arena` + `script.assertions` is a **faithful** subject for
    /// this evidence.
    ///
    /// `false` for a string script: its decidable content lives in the parser's
    /// word / membership / length side channels, and the flat view is bounded or
    /// empty. Re-checking a `sat` model against an empty view passes *vacuously*
    /// — the exact ADR-0061 P0 — so [`EvidenceWithScript::check_outcome`] reports
    /// [`NoCheckReason::UnfaithfulSubject`] rather than a verification.
    pub arena_view_faithful: bool,
}

impl EvidenceWithScript {
    /// Independently re-validates the report against the script it was produced
    /// from, **without re-parsing** (ADR-0384).
    ///
    /// Returns [`NoCheckReason::UnfaithfulSubject`] when the flat arena view is
    /// not a faithful subject (a string script) and the evidence is not one of
    /// the self-contained, arena-independent certificates
    /// ([`Evidence::UnsatWordClash`], [`Evidence::UnsatRegexEmptiness`]) — those
    /// carry their own premises and are re-derived regardless (ADR-0061).
    ///
    /// # Errors
    ///
    /// Propagates [`Evidence::check_outcome`]'s errors.
    pub fn check_outcome(&self) -> Result<EvidenceCheck, SolverError> {
        if !self.arena_view_faithful && !is_subject_independent_evidence(&self.report.evidence) {
            return Ok(EvidenceCheck::NothingToCheck(
                NoCheckReason::UnfaithfulSubject,
            ));
        }
        self.report
            .evidence
            .check_outcome(&self.script.arena, &self.script.assertions)
    }
}

/// Whether this evidence's certificate is **self-contained** — it carries its own
/// premises and [`Evidence::check_outcome`] re-derives it without consulting
/// `(arena, assertions)` (ADR-0061). Those variants are checkable even when the
/// available arena view is the bounded/empty string one.
fn is_subject_independent_evidence(evidence: &Evidence) -> bool {
    matches!(
        evidence,
        Evidence::UnsatWordClash(_)
            | Evidence::UnsatRegexEmptiness { .. }
            | Evidence::UnsatStringLength { .. }
    )
}

/// [`produce_evidence_smtlib`] that **keeps the parsed script**: the report plus
/// the arena and assertion view it was produced against, so a consumer can
/// re-check its own result without re-parsing the text (ADR-0384).
///
/// See [`produce_evidence_smtlib`] for the routing contract (it is this function
/// with the script dropped) and [`EvidenceWithScript`] for why the subject
/// matters.
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text, or any [`SolverError`]
/// from the chosen engine.
pub fn produce_evidence_smtlib_with_script(
    input: &str,
    config: &SolverConfig,
) -> Result<EvidenceWithScript, SolverError> {
    let mut script = axeyum_smtlib::parse_script(input)
        .map_err(|error| SolverError::Parse(error.to_string()))?;
    // A string script is one that used the bounded string/sequence encoding, or one
    // the bounded encoder declined wholesale (word-first fallback). Both cases carry
    // their decidable content in the parser side channels, NOT in the flat arena
    // assertions — so the arena front door cannot see (let alone soundly decide) the
    // real query. Everything else is faithfully represented by the flat view and
    // keeps the full arena certificate ladder.
    let is_string_script = script.uses_bounded_strings || script.word_only_fallback.is_some();
    if !is_string_script {
        let assertions = script.assertions.clone();
        let mut report = produce_evidence(&mut script.arena, &assertions, config)?;
        // Fpa2Bv per-query trust step (task #69). FP → BV lowering happened eagerly
        // during parsing, so `produce_evidence` (which sees only the bit-vector
        // assertions) cannot record it. The parser preserved the FP op-set on the
        // `Script`; attach the trust step here, `certified` iff every FP operator the
        // reduction lowered is structurally exact (see `FpUsage`). Only for an
        // `unsat`-family result: `sat` is replay-checked and `unknown` records no
        // reductions.
        if script.fp_usage.uses_fp && is_unsat_evidence(&report.evidence) {
            report.trusted_steps = with_fpa2bv_step(
                &report.trusted_steps,
                script.fp_usage.fpa2bv_simple_op_certified(),
            );
        }
        return Ok(EvidenceWithScript {
            report,
            script,
            arena_view_faithful: true,
        });
    }

    // String script: delegate the DECISION to the string-capable text front door.
    // `solve_smtlib`'s `sat` is Seq-level replay-checked inside the string routes and
    // its `unsat` is a re-checked theory conflict, so the verdict is already sound;
    // we wrap it without inventing a bounded model. The bounded/word side channels
    // are not re-expressible as a checkable in-tree certificate object here, so the
    // report is the CORRECT verdict recorded honestly (no spurious `checked = true`
    // sat) — a correct-verdict-uncertified report, never a wrong-verdict-certified
    // one.
    let outcome = crate::solve_smtlib(input, config)?;
    let provenance = Provenance::for_query(
        config,
        "smtlib-string-front-door".to_owned(),
        script.assertions.len(),
    );
    let evidence = match outcome.result {
        // The model is the string routes' Seq-level replay-checked witness; wrap it
        // as-is (its faithful re-check is the Seq-level evaluation the route already
        // ran, not an arena replay against the bounded/empty view).
        CheckResult::Sat(model) => Evidence::Sat(model),
        // A word-clash / regex-emptiness / concat-emptiness / length conflict decided
        // the `unsat`; upgrade it to a transferable certified variant where one exists,
        // else a correct bare-but-sound `Evidence::Unsat(None)`.
        CheckResult::Unsat => string_unsat_evidence(input, &mut script, config),
        CheckResult::Unknown(reason) => Evidence::Unknown(reason),
    };
    Ok(EvidenceWithScript {
        report: EvidenceReport {
            evidence,
            provenance,
            trusted_steps: Vec::new(),
        },
        script,
        // The flat view is the bounded/empty one the string routes deliberately
        // do NOT decide against; it is not a checking subject (ADR-0061).
        arena_view_faithful: false,
    })
}

/// Upgrade a string-route `unsat` verdict to the strongest transferable, self-checking
/// [`Evidence`] variant the deciding class admits (ADR-0061):
///
/// 1. **Regex derivative-emptiness** → [`Evidence::UnsatRegexEmptiness`], carrying the
///    kernel-checked Lean module #52 wires into the live path (re-derived from the
///    self-contained `Membership` on re-check — the module string is never trusted).
/// 2. **Word clash** → [`Evidence::UnsatWordClash`], carrying the self-contained,
///    self-checking Alethe [`WordClashCertificate`](crate::WordClashCertificate)
///    (`check()` re-runs the Alethe replay, arena-free — a tampered proof fails).
/// 3. **Length / code-point abstraction** → [`Evidence::UnsatStringLength`], carrying
///    the script's own top-level commands, the named theory lemmas the argument uses,
///    and one Farkas combination per case-split branch (re-derived from the commands
///    on re-check — the carried lemma instances are bound to the conjuncts that
///    license them before any multiplier is read), plus a kernel-checked Lean module
///    over the constructed integers when the conjunctive reconstruction succeeds.
/// 4. Otherwise (concat conflict, or a reconstruction/cap decline) a correct
///    bare-but-sound [`Evidence::Unsat(None)`](Evidence::Unsat).
///
/// The verdict is never changed — this is a pure evidence upgrade over the object the
/// route already decided. Each certificate independently re-checks; a decline is a
/// clean fall-through to the next class, never a fabricated certificate.
///
/// # Why the ORDER puts the length certificate last
///
/// It is the newest and the most generic of the three, and its job is to upgrade what
/// was a bare `Evidence::Unsat(None)` — never to displace a regex-emptiness proof that
/// reconstructs to a kernel-checked Lean module, or a word clash whose Alethe replay
/// is stronger evidence about the same query. Placing a new certifier first has
/// shadowed better ones here before (`quant_instance_set_certificate`, four tests).
fn string_unsat_evidence(
    input: &str,
    script: &mut axeyum_smtlib::Script,
    config: &SolverConfig,
) -> Evidence {
    // (1) Regex derivative-emptiness (kernel-checked Lean).
    if let Some((membership, lean_module)) = crate::membership_unsat_certificate(script, config) {
        return Evidence::UnsatRegexEmptiness {
            membership,
            lean_module,
        };
    }
    // (2) Word clash (self-checking Alethe certificate). Clone the (Copy-element)
    // equalities/disequalities so the immutable borrow of `word_problem` ends before
    // `word_conflict_alethe` takes `&mut script.arena` (mirrors the word route).
    if let Some((eqs, diseqs)) = script
        .word_problem
        .as_ref()
        .map(|wp| (wp.equalities.clone(), wp.disequalities.clone()))
        && let Ok(certificate) = crate::word_conflict_alethe(&mut script.arena, &eqs, &diseqs)
    {
        return Evidence::UnsatWordClash(certificate);
    }
    // (3) Length / code-point abstraction with a Farkas-style linear refutation.
    // This reads the SOURCE s-expressions, not `script.arena`: the arena holds the
    // ADR-0029 bounded packed-BV encoding (or nothing at all under the word-first
    // fallback), which is neither the query nor a checking subject for it.
    if let Ok(commands) = axeyum_smtlib::read_all(input)
        && let Some(certificate) = crate::string_length_cert::string_length_refutation(&commands)
    {
        // Best-effort Lean backing: the conjunctive form reconstructs to a
        // kernel-checked `False` over the constructed integers, a case split does
        // not (yet). A decline is `None`, never a weaker certificate.
        let lean_module = crate::reconstruct_string_length_to_lean_module(&certificate).ok();
        return Evidence::UnsatStringLength {
            certificate,
            lean_module,
        };
    }
    // (4) No transferable certificate yet: the correct, honestly-uncertified verdict.
    Evidence::Unsat(None)
}

/// Like [`produce_evidence`], but when the query is satisfiable, optionally
/// replaces the replay-checked model with a lexicographically minimized
/// replay-checked model over `symbols`.
///
/// This is the evidence-facing "small counterexample" front door for property
/// and verification consumers. It is strict: if the query is satisfiable but
/// minimization cannot prove a minimal model, the returned report is
/// [`Evidence::Unknown`] (or an explicit [`SolverError::Unsupported`] for an
/// unsupported objective sort) rather than silently returning a non-minimal
/// model.
///
/// # Errors
///
/// Returns errors from [`produce_evidence`] or from the model minimizer.
pub fn produce_evidence_minimized(
    arena: &mut TermArena,
    assertions: &[TermId],
    symbols: &[SymbolId],
    config: &SolverConfig,
) -> Result<EvidenceReport, SolverError> {
    let objectives: Vec<crate::ModelMinimizeObjective> = symbols
        .iter()
        .copied()
        .map(crate::ModelMinimizeObjective::Symbol)
        .collect();
    produce_evidence_minimized_with_objectives(arena, assertions, &objectives, config)
}

/// Like [`produce_evidence_minimized`], but accepts per-objective metadata such
/// as signed two's-complement order for bit-vector symbols.
///
/// # Errors
///
/// Returns errors from [`produce_evidence`] or from the model minimizer.
pub fn produce_evidence_minimized_with_objectives(
    arena: &mut TermArena,
    assertions: &[TermId],
    objectives: &[crate::ModelMinimizeObjective],
    config: &SolverConfig,
) -> Result<EvidenceReport, SolverError> {
    let mut report = produce_evidence(arena, assertions, config)?;
    if objectives.is_empty() || !matches!(report.evidence, Evidence::Sat(_)) {
        return Ok(report);
    }

    report.evidence = match crate::minimize_model_objectives_with_config(
        arena, assertions, objectives, config,
    )? {
        ModelMinimizeOutcome::Minimized(model) => Evidence::Sat(model),
        ModelMinimizeOutcome::Unknown(reason) => Evidence::Unknown(reason),
        ModelMinimizeOutcome::Infeasible => {
            return Err(SolverError::Backend(
                "produce_evidence_minimized: base query was sat but minimization found unsat"
                    .to_owned(),
            ));
        }
    };
    Ok(report)
}

fn uflia_alethe_evidence_report(
    arena: &mut TermArena,
    assertions: &[TermId],
    provenance: &Provenance,
) -> Option<EvidenceReport> {
    Some(EvidenceReport {
        evidence: Evidence::UnsatArithAletheProof(uflia_alethe_certificate(arena, assertions)?),
        provenance: provenance.clone(),
        trusted_steps: Vec::new(),
    })
}

fn bounded_int_blast_evidence(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<(Evidence, Vec<TrustStep>)>, SolverError> {
    let Some(cert) = certify_bounded_int_blast(arena, assertions)? else {
        return Ok(None);
    };
    Ok(Some((
        Evidence::UnsatBoundedIntBlast(cert),
        trust_steps(&[
            (TrustId::IntBlast, true),
            (TrustId::Tseitin, true),
            (TrustId::SatRefutation, true),
        ]),
    )))
}

fn finite_domain_enum_evidence(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<(Evidence, Vec<TrustStep>)>, SolverError> {
    match certify_finite_bv_by_enumeration(arena, assertions, TERM_LEVEL_CERT_BITS) {
        Ok(CertifyOutcome::CertifiedUnsat { cases }) => Ok(Some((
            Evidence::UnsatFiniteDomainEnum {
                cases,
                max_total_bits: TERM_LEVEL_CERT_BITS,
            },
            trust_steps(&[(TrustId::TermLevelEnum, true)]),
        ))),
        Ok(CertifyOutcome::Satisfiable(_)) => Err(SolverError::Backend(
            "soundness alarm: backend reported unsat but finite-domain enumeration found a model"
                .to_owned(),
        )),
        Ok(CertifyOutcome::DomainTooLarge { .. }) | Err(SolverError::Unsupported(_)) => Ok(None),
        Err(error) => Err(error),
    }
}

fn small_pre_solve_array_axiom_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<ArrayAxiomRefutationCertificate> {
    const PRE_SOLVE_ARRAY_AXIOM_DAG_LIMIT: u64 = 256;

    let stats = TermStats::compute(arena, assertions);
    if stats.dag_nodes > PRE_SOLVE_ARRAY_AXIOM_DAG_LIMIT {
        return None;
    }
    crate::array_axiom::array_axiom_refutation(arena, assertions)
}

fn direct_structural_unsat_evidence(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<(Evidence, Vec<TrustStep>)> {
    if let Some(evidence) = quantified_structural_unsat_evidence(arena, assertions) {
        return Some((evidence, Vec::new()));
    }
    if let Some(cert) = crate::ufbv_finite::finite_domain_pigeonhole_refutation(arena, assertions) {
        return Some((Evidence::UnsatFiniteDomainPigeonhole(cert), Vec::new()));
    }
    if let Some(cert) = crate::ufbv_finite::bool_uf_exhaustive_refutation(arena, assertions) {
        return Some((Evidence::UnsatBoolUfExhaustive(cert), Vec::new()));
    }
    if let Some(cert) = crate::bool_euf::bool_euf_exhaustive_refutation(arena, assertions) {
        return Some((Evidence::UnsatBoolEufExhaustive(cert), Vec::new()));
    }
    if let Some(cert) = crate::bool_euf::bool_euf_online_refutation(arena, assertions) {
        return Some((Evidence::UnsatBoolEufOnline(cert), Vec::new()));
    }
    if let Some(cert) = crate::uf_arith::uf_arith_congruence_refutation(arena, assertions) {
        return Some((Evidence::UnsatUfArithCongruence(cert), Vec::new()));
    }
    if let Some(cert) =
        crate::datatype_acyclicity::datatype_structural_refutation(arena, assertions)
    {
        return Some((Evidence::UnsatDatatypeStructural(cert), Vec::new()));
    }
    if let Some(cert) =
        crate::bv_forall_nonconstant::bv_forall_nonconstant_refutation(arena, assertions)
    {
        return Some((Evidence::UnsatBvForallNonconstant(cert), Vec::new()));
    }
    if let Some(cert) = crate::bv_uf_local::bv_uf_local_refutation(arena, assertions) {
        return Some((Evidence::UnsatBvUfLocal(cert), Vec::new()));
    }
    if let Some(cert) = crate::set_cardinality::set_cardinality_refutation(arena, assertions) {
        return Some((Evidence::UnsatSetCardinality(cert), Vec::new()));
    }
    if let Some(cert) = crate::bv_defined_enum::bv_defined_enum_refutation(arena, assertions) {
        return Some((Evidence::UnsatBvDefinedEnum(cert), Vec::new()));
    }
    if let Some(cert) =
        crate::array_finite::finite_array_extensionality_refutation(arena, assertions)
    {
        return Some((Evidence::UnsatFiniteArrayExtensionality(cert), Vec::new()));
    }
    if let Some(cert) = crate::array_finite::bool_array_read_collapse_refutation(arena, assertions)
    {
        return Some((Evidence::UnsatBoolArrayReadCollapse(cert), Vec::new()));
    }
    if let Some(cert) = crate::term_identity::term_identity_refutation(arena, assertions) {
        return Some((Evidence::UnsatTermIdentity(cert), Vec::new()));
    }
    if let Some(cert) = crate::bool_simplify::bool_simplification_refutation(arena, assertions) {
        return Some((Evidence::UnsatBoolSimplification(cert), Vec::new()));
    }
    if let Some(cert) = crate::array_axiom::array_axiom_refutation(arena, assertions) {
        return Some((Evidence::UnsatArrayAxiom(cert), Vec::new()));
    }
    if let Some(cert) = crate::abv::const_array_default_mismatch_refutation(arena, assertions) {
        return Some((Evidence::UnsatConstArrayDefaultMismatch(cert), Vec::new()));
    }
    if let Some(cert) = crate::abv::store_chain_readback_refutation(arena, assertions) {
        return Some((Evidence::UnsatStoreChainReadback(cert), Vec::new()));
    }
    if let Some(cert) = crate::abv::cross_store_array_disequality_refutation(arena, assertions) {
        return Some((Evidence::UnsatCrossStoreArrayDisequality(cert), Vec::new()));
    }
    if let Some(cert) = crate::array_bv_abs::bv_abstraction_refutation(arena, assertions) {
        return Some((Evidence::UnsatBvAbstraction(cert), Vec::new()));
    }
    if let Some(cert) = crate::array_memcpy::two_byte_memcpy_refutation(arena, assertions) {
        return Some((Evidence::UnsatTwoByteMemcpy(cert), Vec::new()));
    }
    if let Some(cert) = crate::array_sort2::two_element_bubble_sort_refutation(arena, assertions) {
        return Some((Evidence::UnsatTwoElementBubbleSort(cert), Vec::new()));
    }
    if let Some(cert) = crate::array_sort2::two_element_selection_sort_refutation(arena, assertions)
    {
        return Some((Evidence::UnsatTwoElementSelectionSort(cert), Vec::new()));
    }
    if let Some(cert) = crate::array_xor_swap::two_cell_xor_swap_refutation(arena, assertions) {
        return Some((Evidence::UnsatTwoCellXorSwap(cert), Vec::new()));
    }
    if let Some(cert) =
        crate::array_xor_swap::two_byte_xor_swap_roundtrip_refutation(arena, assertions)
    {
        return Some((Evidence::UnsatTwoByteXorSwapRoundtrip(cert), Vec::new()));
    }
    if let Some(cert) = crate::array_binary_search::binary_search16_refutation(arena, assertions) {
        return Some((Evidence::UnsatBinarySearch16(cert), Vec::new()));
    }
    if let Some(cert) = crate::array_fifo::fifo_bc04_refutation(arena, assertions) {
        return Some((Evidence::UnsatFifoBc04(cert), Vec::new()));
    }
    crate::array_write_chain::aligned_write_chain_commutation_refutation(arena, assertions).map(
        |cert| {
            (
                Evidence::UnsatAlignedWriteChainCommutation(cert),
                Vec::new(),
            )
        },
    )
}

/// Tries each **zero-trust-hole** Alethe certificate emitter in turn, returning the
/// first that produces a [`check_alethe`]-validated refutation closing to `(cl)`:
///
/// 1. [`crate::prove_qf_abv_unsat_alethe`] — the array read-over-write-same cert
///    (internal array rule) or direct equal-array select-congruence cert (standard
///    equality rules, no array axiom);
/// 2. [`crate::prove_qf_uf_unsat_alethe`] — the pure EUF congruence cert over
///    uninterpreted functions and carrier-sort equalities;
/// 3. [`crate::prove_qf_ufbv_unsat_alethe`] — the Ackermann (`QF_UFBV`) cert (derives
///    each functional-consistency constraint by `eq_congruent`);
/// 4. [`crate::prove_qf_abv_unsat_alethe_via_elimination`] — the array-elimination
///    (`QF_ABV`) cert (derives each read-consistency constraint by `eq_congruent`);
/// 5. [`crate::prove_qf_dt_unsat_alethe_via_simplification`] — the datatype
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
    if let Some(proof) = crate::prove_qf_uf_unsat_alethe(arena, assertions)
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

/// Tries the **mixed arithmetic-sorted UF + linear-arithmetic** zero-trust-hole
/// Alethe emitter ([`crate::prove_qf_uflia_unsat_alethe`]), returning a
/// [`crate::check_alethe_lra`]-validated refutation for a `QF_UFLIA`/`QF_UFLRA`
/// `unsat` whose conflict is congruence-then-arithmetic (e.g. `f(x)=1 ∧ f(y)=2 ∧
/// x=y`). It needs `&mut TermArena` because the Ackermann reduction interns fresh
/// abstraction symbols, so it sits between [`zero_trust_alethe_certificate`] (the
/// `&mut` array/UF-bitvector path) and [`arith_alethe_certificate`] (the `&` pure
/// LIA/LRA path).
///
/// The emitter is self-validating (returns `Some` only after `check_alethe_lra`
/// accepts) and declines cheaply outside its fragment — BV-sorted UF (owned by the
/// bit-vector path), arrays/datatypes/quantifiers, and any non-`unsat` residual —
/// so trying it after [`zero_trust_alethe_certificate`] never shadows the BV
/// zero-trust cert, and the defensive `check_alethe_lra` re-gate mirrors the other
/// arithmetic call sites. A returned proof carries **no trusted reduction step**.
fn uflia_alethe_certificate(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    if let Some(proof) = crate::prove_qf_uflia_unsat_alethe(arena, assertions)
        && matches!(crate::check_alethe_lra(&proof), Ok(true))
    {
        return Some(proof);
    }
    if let Some(proof) = crate::prove_uflia_opaque_unsat_alethe(arena, assertions)
        && matches!(crate::check_alethe_lra(&proof), Ok(true))
    {
        return Some(proof);
    }
    if let Some(proof) = crate::prove_uflra_unsat_alethe(arena, assertions)
        && matches!(crate::check_alethe_lra(&proof), Ok(true))
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

/// Tries the **finite-expansion guarded-`Int` quantifier** Alethe emitter
/// ([`prove_finite_int_quant_unsat_alethe`]), returning a
/// [`check_alethe_lra_guarded_inst`]-validated refutation together with the
/// [`GuardedUniversalForm`] the [`Evidence::UnsatGuardedQuantAletheProof`] carries
/// (so the variant re-checks without the original arena).
///
/// The emitter is self-validating (returns `Some` only after the combined checker
/// accepts) and declines cheaply outside its slice — anything that is not exactly
/// one guarded-finite-`Int` universal `∀x:Int. (lo<=x<=hi) => inner` (with a
/// linear-integer comparison inner) plus quantifier-free linear-integer side
/// assertions, or whose finite expansion is not integer-`unsat`. So it never
/// shadows the ground certs (which already declined on the quantifier) and a
/// returned proof is genuinely re-checkable. The defensive re-gate mirrors the
/// other arithmetic call sites; the matching `universal` form is re-derived by the
/// shared detection.
fn guarded_quant_alethe_certificate(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<(Vec<AletheCommand>, GuardedUniversalForm)> {
    let proof = prove_finite_int_quant_unsat_alethe(arena, assertions)?;
    let universal = guarded_universal_form(arena, assertions)?;
    if matches!(
        check_alethe_lra_guarded_inst_against(&universal, &proof, arena, assertions),
        Ok(true)
    ) {
        Some((proof, universal))
    } else {
        None
    }
}

/// Tries the **UF-bodied** finite-expansion guarded-`Int` quantifier Alethe emitter
/// ([`prove_finite_int_quant_unsat_uf_alethe`]), returning a
/// [`check_alethe_lra_guarded_inst`]-validated refutation together with the
/// [`GuardedUniversalForm`] the [`Evidence::UnsatGuardedQuantAletheProof`] carries.
///
/// The emitter is self-validating (returns `Some` only after the combined checker
/// accepts) and declines cheaply outside its slice — anything that is not exactly
/// one guarded-finite-`Int` universal `∀x:Int. (lo<=x<=hi) => (= (f x) c)` whose
/// expanded residual contains an arithmetic-sorted uninterpreted application and is
/// LIA-`unsat` after Ackermann abstraction. Ordered AFTER the pure-LIA finite-`∀`
/// cert (which declines a UF body), so it never shadows it, and the matching
/// `universal` form is re-derived by the shared UF-aware detection.
fn guarded_quant_uf_alethe_certificate(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<(Vec<AletheCommand>, GuardedUniversalForm)> {
    let proof = prove_finite_int_quant_unsat_uf_alethe(arena, assertions)?;
    let universal = guarded_universal_form_uf(arena, assertions)?;
    if matches!(
        check_alethe_lra_guarded_inst_against(&universal, &proof, arena, assertions),
        Ok(true)
    ) {
        Some((proof, universal))
    } else {
        None
    }
}

/// Tries the **`bv2nat`-bound** refutation cert: a query whose `unsat` rests on
/// the provable range `0 <= bv2nat_W(b) <= 2^W - 1` of a `W`-bit bit-vector (e.g.
/// `bv2nat(x) >= 16` for a 4-bit `x`). The exact integer refuters reject a raw
/// `bv2nat(b)` subterm, so such a query is otherwise a bare `Evidence::Unsat(None)`.
///
/// It mirrors [`crate::auto`]'s `refute_bv2nat_out_of_range`: on an isolated clone
/// of the arena it [`abstract_bv2nat_for_refutation`]s each distinct `bv2nat(b)`
/// to a fresh `Int` symbol `n` plus the **trusted** range axiom `0 <= n <= 2^W-1`
/// (the int↔BV-width bridge — ledgered as [`TrustId::IntBlast`]). The resulting
/// query is a sound relaxation (every model of the original induces one of the
/// abstraction), so an `unsat` of the abstraction transfers to the original. The
/// abstraction is **pure LIA**, so [`crate::prove_lia_unsat_alethe`] emits a
/// `lia_generic` cert over it — the bulk of the refutation is **certified**
/// (re-derived by [`crate::check_alethe_lra`]); only the range axiom is trusted.
///
/// Returns the checked proof together with its [`TrustStep`]s
/// (`IntBlast`: trusted/`false`, `Farkas`: certified/`true`), or `None` when there
/// is no abstractable `bv2nat` (so the plain LIA/UFLIA paths own their queries —
/// this declines for them) or the abstraction is not LIA-`unsat`. Ordered AFTER
/// [`arith_alethe_certificate`] (which declines a raw `bv2nat` subterm) so it
/// never shadows the zero-trust certs.
///
/// The returned proof is over the **abstracted** assertions (the fresh `!bv2nat.*`
/// symbols), so [`Evidence::check`] re-checks the LIA proof self-containedly
/// (`check_alethe_lra` reads only the carried Alethe commands, not the arena).
fn bv2nat_bound_certificate(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<(Vec<AletheCommand>, Vec<TrustStep>)> {
    use crate::bv2nat_bound::abstract_bv2nat_for_refutation;

    // Abstract on an isolated clone: the fresh `!bv2nat.*` symbols and rewritten
    // terms must never leak into the caller's arena (or any later sat model).
    let mut scratch = arena.clone();
    let relaxed = abstract_bv2nat_for_refutation(&mut scratch, assertions).ok()??;
    // The abstraction is pure LIA after divmod elimination (parity with the
    // refuter in `auto`); emit the `lia_generic` cert over it. `prove_lia_unsat_alethe`
    // self-validates and internally re-runs `check_with_lia_simplex`, so a non-`unsat`
    // abstraction (or one outside the LIA fragment) yields `None`.
    let linear = axeyum_rewrite::eliminate_int_divmod(&mut scratch, &relaxed).ok()?;
    let proof = crate::prove_lia_unsat_alethe(&scratch, &linear)?;
    if !matches!(crate::check_alethe_lra(&proof), Ok(true)) {
        return None;
    }
    // The LIA refutation is re-derived (certified); the `bv2nat`-range abstraction
    // is the one trusted step (the int↔BV-width bridge, ledgered as `IntBlast`).
    let steps = trust_steps(&[(TrustId::IntBlast, false), (TrustId::Farkas, true)]);
    Some((proof, steps))
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
    deadline: Option<Instant>,
) -> (Option<UnsatProof>, Vec<TrustStep>) {
    use crate::proof::{export_datatype_unsat_proof, export_qf_aufbv_unsat_proof_within};

    let (has_array, has_func, has_datatype) = reduction_fragment_flags(arena, assertions);

    // Arrays + uninterpreted functions → BV. Only the reductions that actually
    // fire (present in the fragment) are recorded as trust holes.
    if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        return (None, Vec::new());
    }
    if let Ok(UnsatProofOutcome::Proved(proof)) =
        export_qf_aufbv_unsat_proof_within(arena, assertions, deadline)
    {
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
    /// been re-checked, so `Proved` means an independently verified proof. For a
    /// fragment whose `unsat` is still bare, `Proved` is the deciding engine's
    /// verdict with nothing re-derived — ask
    /// [`EvidenceReport::evidence`]`.`[`is_certified`](Evidence::is_certified)
    /// or re-run [`Evidence::check_outcome`] to tell the two apart (ADR-0384).
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
        | Evidence::UnsatGuardedQuantAletheProof { .. }
        | Evidence::UnsatTermLevel { .. }
        | Evidence::UnsatFiniteDomainEnum { .. }
        | Evidence::UnsatBvDefinedEnum(_)
        | Evidence::UnsatBvForallNonconstant(_)
        | Evidence::UnsatIntEuclideanResidue(_)
        | Evidence::UnsatIntAffineGrowth(_)
        | Evidence::UnsatIntNestedXor(_)
        | Evidence::UnsatClosedUniversalCounterexample(_)
        | Evidence::UnsatVacuousExistsUniversalCounterexample(_)
        | Evidence::UnsatNegatedExistentialWitness(_)
        | Evidence::UnsatBvAlternationCounterexample(_)
        | Evidence::UnsatBvConjunctiveUniversalInstance(_)
        | Evidence::UnsatBvPositiveUniversalInstanceSet(_)
        | Evidence::UnsatBvPairedExistentialTransfer(_)
        | Evidence::UnsatEqualityPartition(_)
        | Evidence::UnsatQuantifiedCounterexampleCover(_)
        | Evidence::UnsatQuantInstanceSet(_)
        | Evidence::UnsatBvUfLocal(_)
        | Evidence::UnsatSetCardinality(_)
        | Evidence::UnsatFarkas(_)
        | Evidence::UnsatLraDpll(_)
        | Evidence::UnsatArithDpll(_)
        | Evidence::UnsatSos { .. }
        | Evidence::UnsatIntQuadraticNegativeDiscriminant(_)
        | Evidence::UnsatIntUnivariatePoly(_)
        | Evidence::UnsatNraEvenPower(_)
        | Evidence::UnsatRealZeroProduct(_)
        | Evidence::UnsatRealProduct(_)
        | Evidence::UnsatRealHandelman(_)
        | Evidence::UnsatMonomialBound(_)
        | Evidence::UnsatDiophantine { .. }
        | Evidence::UnsatBoundedIntBlast(_)
        | Evidence::UnsatFiniteDomainPigeonhole(_)
        | Evidence::UnsatBoolUfExhaustive(_)
        | Evidence::UnsatBoolEufExhaustive(_)
        | Evidence::UnsatBoolEufOnline(_)
        | Evidence::UnsatUfArithCongruence(_)
        | Evidence::UnsatDatatypeStructural(_)
        | Evidence::UnsatFiniteArrayExtensionality(_)
        | Evidence::UnsatBoolArrayReadCollapse(_)
        | Evidence::UnsatArrayAxiom(_)
        | Evidence::UnsatConstArrayDefaultMismatch(_)
        | Evidence::UnsatStoreChainReadback(_)
        | Evidence::UnsatCrossStoreArrayDisequality(_)
        | Evidence::UnsatTermIdentity(_)
        | Evidence::UnsatBoolSimplification(_)
        | Evidence::UnsatBvAbstraction(_)
        | Evidence::UnsatAlignedWriteChainCommutation(_)
        | Evidence::UnsatTwoByteMemcpy(_)
        | Evidence::UnsatTwoElementBubbleSort(_)
        | Evidence::UnsatTwoElementSelectionSort(_)
        | Evidence::UnsatTwoCellXorSwap(_)
        | Evidence::UnsatTwoByteXorSwapRoundtrip(_)
        | Evidence::UnsatBinarySearch16(_)
        | Evidence::UnsatFifoBc04(_)
        | Evidence::UnsatRegexEmptiness { .. }
        | Evidence::UnsatWordClash(_)
        | Evidence::UnsatStringLength { .. } => {
            // Three-valued so the two very different "not verified" cases stay
            // apart (ADR-0384): a certificate that FAILS is a soundness alarm,
            // while a bare `unsat` has nothing to check and keeps the historical
            // `Proved` (the verdict is the engine's, honestly uncertified — read
            // `report.evidence.is_certified()` / `report.trusted_steps` to tell
            // the two apart). Collapsing this to `check(..)? == false` would turn
            // every uncertified fragment's proof into an error.
            match report.evidence.check_outcome(arena, &query)? {
                EvidenceCheck::Failed => {
                    return Err(SolverError::Backend(
                        "prove: refutation of the negated goal failed its own check".to_owned(),
                    ));
                }
                EvidenceCheck::Verified | EvidenceCheck::NothingToCheck(_) => {}
            }
            Ok(ProofOutcome::Proved(Box::new(report)))
        }
    }
}

/// Like [`prove`], but when the goal is disproved, returns a replay-checked
/// countermodel that is lexicographically minimized over `symbols`.
///
/// This is the proof-facing counterpart of [`produce_evidence_minimized`]. The
/// default [`prove`] API remains unchanged; callers opt into the stricter
/// minimization contract when they want a deterministic "small failing input".
///
/// If the negated goal is satisfiable but minimization is undecided, the result
/// is [`ProofOutcome::Unknown`] rather than a non-minimal [`ProofOutcome::Disproved`].
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if a requested objective symbol has an
/// unsupported sort, or propagates errors from [`prove`] and the minimizer.
pub fn prove_minimized(
    arena: &mut TermArena,
    hypotheses: &[TermId],
    goal: TermId,
    symbols: &[SymbolId],
    config: &SolverConfig,
) -> Result<ProofOutcome, SolverError> {
    let objectives: Vec<crate::ModelMinimizeObjective> = symbols
        .iter()
        .copied()
        .map(crate::ModelMinimizeObjective::Symbol)
        .collect();
    prove_minimized_with_objectives(arena, hypotheses, goal, &objectives, config)
}

/// Like [`prove_minimized`], but accepts per-objective metadata such as signed
/// two's-complement order for bit-vector symbols.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if a requested objective symbol has an
/// unsupported sort or unsupported metadata, or propagates errors from
/// [`prove`] and the minimizer.
pub fn prove_minimized_with_objectives(
    arena: &mut TermArena,
    hypotheses: &[TermId],
    goal: TermId,
    objectives: &[crate::ModelMinimizeObjective],
    config: &SolverConfig,
) -> Result<ProofOutcome, SolverError> {
    let outcome = prove(arena, hypotheses, goal, config)?;
    if objectives.is_empty() || !matches!(outcome, ProofOutcome::Disproved(_)) {
        return Ok(outcome);
    }

    let negated_goal = arena.not(goal)?;
    let mut query: Vec<TermId> = hypotheses.to_vec();
    query.push(negated_goal);

    match crate::minimize_model_objectives_with_config(arena, &query, objectives, config)? {
        ModelMinimizeOutcome::Minimized(model) => Ok(ProofOutcome::Disproved(model)),
        ModelMinimizeOutcome::Unknown(reason) => Ok(ProofOutcome::Unknown(reason)),
        ModelMinimizeOutcome::Infeasible => Err(SolverError::Backend(
            "prove_minimized: negated goal was sat but minimization found unsat".to_owned(),
        )),
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
    let mut has_uninterpreted_sort = false;
    let mut has_datatype = false;
    let mut seen = BTreeSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.sort_of(term) {
            Sort::Real => has_real = true,
            Sort::BitVec(_) | Sort::RoundingMode | Sort::Float { .. } => has_bitvec = true,
            Sort::Array { .. } => has_array = true,
            Sort::Int => has_int = true,
            // A datatype-sorted subterm signals a datatype query even when every
            // top-level asserted term is Bool/BitVec (e.g. `select(mk(a,b), 0) =
            // #b00`): it must route to `solve`, not the raw BV bit-blaster.
            Sort::Datatype(_) => has_datatype = true,
            Sort::Uninterpreted(_) => has_uninterpreted_sort = true,
            // `Bool` signals no theory. `Seq` is a no-op for now (TODO(P2.7 A.1b):
            // no sequence evidence route exists yet and no front-end produces a
            // `Seq` sort, so this is unreachable today; add a route when sequences
            // land).
            Sort::Bool | Sort::Seq(_) => {}
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

    let extra = has_array
        || has_int
        || has_func
        || has_quantifier
        || has_datatype
        || has_uninterpreted_sort;
    if !has_real && !extra {
        EvidenceRoute::QfBv // only bit-vectors and Booleans
    } else if has_real && !has_bitvec && !extra {
        EvidenceRoute::PureReal // only reals and Booleans
    } else {
        EvidenceRoute::Other
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::UnknownKind;

    /// A `QF_BV` query that is unsatisfiable and small enough that the whole
    /// certificate ladder is available: `a = a + 1` over 8 bits.
    fn unsat_bv_query() -> (TermArena, Vec<TermId>) {
        let mut arena = TermArena::new();
        let symbol = arena.declare("a", Sort::BitVec(8)).expect("declare");
        let a = arena.var(symbol);
        let one = arena.bv_const(8, 1).expect("const");
        let sum = arena.bv_add(a, one).expect("bvadd");
        let assertion = arena.eq(a, sum).expect("eq");
        (arena, vec![assertion])
    }

    /// ADR-0384 (A3): a bare `unsat` carries no certificate, so re-validating it
    /// must NOT read as "checked". Before the fix `check` returned `Ok(true)`,
    /// so `if evidence.check(..)? { trust }` passed on an empty set.
    #[test]
    fn bare_unsat_is_nothing_to_check_never_verified() {
        let (arena, assertions) = unsat_bv_query();
        let evidence = Evidence::Unsat(None);

        assert_eq!(
            evidence.check_outcome(&arena, &assertions).expect("check"),
            EvidenceCheck::NothingToCheck(NoCheckReason::UncertifiedUnsat)
        );
        assert!(
            !evidence.check(&arena, &assertions).expect("check"),
            "a bare unsat must not pass the boolean check"
        );
        assert!(!evidence.is_certified());
    }

    /// ADR-0384 (A3): an `unknown` claims nothing, so there is nothing to
    /// validate — and that is not a pass either.
    #[test]
    fn unknown_is_nothing_to_check_never_verified() {
        let (arena, assertions) = unsat_bv_query();
        let evidence = Evidence::Unknown(UnknownReason {
            kind: UnknownKind::Timeout,
            detail: "test".to_owned(),
        });

        assert_eq!(
            evidence.check_outcome(&arena, &assertions).expect("check"),
            EvidenceCheck::NothingToCheck(NoCheckReason::Undecided)
        );
        assert!(!evidence.check(&arena, &assertions).expect("check"));
    }

    /// ADR-0384 (A3): the tightening must not weaken a genuine certificate — a
    /// certified `QF_BV` `unsat` still re-validates as `Verified`/`true`.
    #[test]
    fn certified_unsat_still_verifies() {
        let (arena, assertions) = unsat_bv_query();
        let report =
            produce_qf_bv_evidence(&arena, &assertions, &SolverConfig::new()).expect("evidence");

        assert!(
            report.evidence.is_certified(),
            "expected a certificate, got {}",
            report.evidence.kind_label()
        );
        assert_eq!(
            report
                .evidence
                .check_outcome(&arena, &assertions)
                .expect("check"),
            EvidenceCheck::Verified
        );
        assert!(report.evidence.check(&arena, &assertions).expect("check"));
    }

    /// Installing [`SolverConfig::proof_progress`] on the DRAT certificate route
    /// (i) actually fires the sink and (ii) does not change the exported
    /// certificate — a pure observability hook, exactly like `axeyum_cnf`'s own
    /// no-behaviour-change guarantee on the search underneath it. Calls
    /// `drat_qf_bv_evidence` directly (as `tampered_certificate_fails_rather_than_reading_as_unchecked`
    /// already does via `export_qf_bv_unsat_proof`) to exercise the plain DRAT
    /// route without depending on the term-level-enumeration/Alethe routing
    /// thresholds above it.
    #[test]
    fn proof_progress_sink_fires_and_does_not_change_the_certificate() {
        let (arena, assertions) = unsat_bv_query();
        let (tx, rx) = std::sync::mpsc::channel();
        let progress = crate::backend::ProofProgress::new(1, tx);

        let (with_progress, _) =
            drat_qf_bv_evidence(&arena, &assertions, None, Some(&progress), None)
                .expect("evidence with a progress sink installed");
        let (without_progress, _) = drat_qf_bv_evidence(&arena, &assertions, None, None, None)
            .expect("evidence with no progress sink");

        match (&with_progress, &without_progress) {
            (Evidence::Unsat(Some(a)), Evidence::Unsat(Some(b))) => {
                assert_eq!(
                    a, b,
                    "installing a progress sink must not change the exported DRAT certificate"
                );
            }
            other => panic!("expected a DRAT-certified unsat both ways, got {other:?}"),
        }

        let snapshots: Vec<_> = rx.try_iter().collect();
        assert!(
            !snapshots.is_empty(),
            "an installed sink must fire at least once (the terminal report)"
        );
    }

    /// The checking-stage counterpart of the search-side test above: a
    /// `check_progress` sink observes the checking stage — the one that ran for
    /// ~6 h unbounded and unobserved on `neg-fp16-add-monotone-rne.smt2` —
    /// without changing the exported certificate.
    ///
    /// With no bound installed the budget admits the backward LRAT certification
    /// route (ADR-0613), so that is the stage that reports here. It is not
    /// step-interruptible, so it reports exactly twice: opening and closing.
    /// `crate::proof::tests::the_reference_route_still_reports_both_of_its_sub_stages`
    /// covers the forward route's own observability.
    #[test]
    fn check_progress_sink_fires_and_does_not_change_the_certificate() {
        let (arena, assertions) = unsat_bv_query();
        let (tx, rx) = std::sync::mpsc::channel();
        let check_progress = crate::backend::CheckProgress::new(1, None, tx);

        let (with_progress, _) =
            drat_qf_bv_evidence(&arena, &assertions, None, None, Some(&check_progress))
                .expect("evidence with a checking-progress sink installed");
        let (without_progress, _) = drat_qf_bv_evidence(&arena, &assertions, None, None, None)
            .expect("evidence with no checking-progress sink");

        match (&with_progress, &without_progress) {
            (Evidence::Unsat(Some(a)), Evidence::Unsat(Some(b))) => {
                assert_eq!(
                    a, b,
                    "installing a checking-progress sink must not change the exported certificate"
                );
            }
            other => panic!("expected a DRAT-certified unsat both ways, got {other:?}"),
        }

        let snapshots: Vec<crate::proof::CheckingProgress> = rx.try_iter().collect();
        assert!(
            !snapshots.is_empty(),
            "an installed checking-progress sink must fire at least once (the terminal report)"
        );
        let backward: Vec<_> = snapshots
            .iter()
            .filter_map(|event| match event {
                crate::proof::CheckingProgress::BackwardLratCertify(snapshot) => Some(*snapshot),
                _ => None,
            })
            .collect();
        assert_eq!(
            backward.len(),
            2,
            "the backward certify stage must report one opening and one closing \
             snapshot, got {backward:?}"
        );
        assert!(!backward[0].finished && backward[1].finished);
        assert!(
            backward[1].certified,
            "this query is unsat with a RUP-only proof, so it must certify"
        );
    }

    /// A checking-stage deadline that has already expired before checking even
    /// starts must yield the honest, uncertified `Evidence::Unsat(None)` — NOT
    /// an error, and NOT the certified `Evidence::Unsat(Some(_))` a completed
    /// check would produce. This is the checking-side half of ADR-0384 (A4)'s
    /// "a timeout is not a pass" guarantee; `expired_deadline_yields_a_decided_uncertified_unsat`
    /// covers the search-side half.
    #[test]
    fn an_expired_check_deadline_still_decides_but_does_not_certify() {
        let (arena, assertions) = unsat_bv_query();
        // Ample time for the search (so it actually reaches `unsat`), but the
        // checking stage inherits this SAME deadline, so it starts already
        // spent by the time we tamper with it below via a synthetic path: call
        // the lower-level exporter directly with an already-expired deadline
        // dedicated to checking, bypassing the search deadline entirely.
        let outcome = crate::proof::export_qf_bv_unsat_proof_within_with_check_budget(
            &arena,
            &assertions,
            None,
            crate::proof::CheckBudget {
                deadline: Instant::now().checked_sub(Duration::from_secs(1)),
                ..crate::proof::CheckBudget::default()
            },
        )
        .expect("a checking-stage timeout is an outcome, not an error");
        assert_eq!(
            outcome,
            UnsatProofOutcome::Inconclusive,
            "an expired checking deadline must never be reported as Proved"
        );
    }

    /// ADR-0384 (A3): `Failed` (a certificate that does not hold up — a soundness
    /// alarm) stays distinguishable from `NothingToCheck` (no certificate at
    /// all). A boolean cannot express that difference, which is why `prove` can
    /// keep an uncertified verdict while still erroring on a bad certificate.
    #[test]
    fn tampered_certificate_fails_rather_than_reading_as_unchecked() {
        let (arena, assertions) = unsat_bv_query();
        let proof = match crate::proof::export_qf_bv_unsat_proof(&arena, &assertions) {
            Ok(UnsatProofOutcome::Proved(proof)) => proof,
            other => panic!("expected an exported proof, got {other:?}"),
        };
        // Drop the refutation's steps: the DIMACS still parses, but the proof no
        // longer derives the empty clause.
        let tampered = Evidence::Unsat(Some(UnsatProof {
            dimacs: proof.dimacs,
            drat: String::new(),
            lrat: None,
        }));

        assert_eq!(
            tampered.check_outcome(&arena, &assertions).expect("check"),
            EvidenceCheck::Failed
        );
        assert!(!tampered.check(&arena, &assertions).expect("check"));
        // `is_certified` is the STATIC question and still says yes — only the
        // checker can tell you the certificate is bad.
        assert!(tampered.is_certified());
    }

    /// ADR-0384 (A3): replaying a model against zero assertions succeeds
    /// vacuously (the ADR-0061 bounded/empty-view P0). It is reported as
    /// nothing-checked, never as a verification.
    #[test]
    fn sat_model_against_an_empty_subject_is_nothing_to_check() {
        let mut arena = TermArena::new();
        let symbol = arena.declare("a", Sort::BitVec(4)).expect("declare");
        let a = arena.var(symbol);
        let five = arena.bv_const(4, 5).expect("const");
        let assertion = arena.eq(a, five).expect("eq");
        let report =
            produce_qf_bv_evidence(&arena, &[assertion], &SolverConfig::new()).expect("evidence");
        assert!(matches!(report.evidence, Evidence::Sat(_)));

        assert_eq!(
            report.evidence.check_outcome(&arena, &[]).expect("check"),
            EvidenceCheck::NothingToCheck(NoCheckReason::EmptySubject)
        );
        assert!(!report.evidence.check(&arena, &[]).expect("check"));
        // Against the real subject it verifies.
        assert!(report.evidence.check(&arena, &[assertion]).expect("check"));
    }

    /// ADR-0384 (A4): proof production honors the caller's deadline. An expired
    /// deadline yields the DECIDED-but-uncertified outcome — a bare `unsat` with
    /// `SatRefutation` recorded uncertified — never an `Err` and never an
    /// `unknown`, and without re-running the search.
    #[test]
    fn expired_deadline_yields_a_decided_uncertified_unsat() {
        let (arena, assertions) = unsat_bv_query();
        let expired = Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("instant");

        let started = Instant::now();
        let (evidence, steps) = drat_qf_bv_evidence(&arena, &assertions, Some(expired), None, None)
            .expect("no error on timeout");
        let elapsed = started.elapsed();

        assert!(
            matches!(evidence, Evidence::Unsat(None)),
            "a spent proof budget must keep the verdict, got {}",
            evidence.kind_label()
        );
        assert!(
            !matches!(evidence, Evidence::Unknown(_)),
            "proof-production timeout must not undecide the query"
        );
        let sat_refutation = steps
            .iter()
            .find(|step| step.id == TrustId::SatRefutation)
            .expect("SatRefutation trust step recorded");
        assert!(
            !sat_refutation.certified,
            "no proof was produced, so the SAT refutation is not certified"
        );
        // And it is reported honestly by the checker: nothing was validated.
        assert_eq!(
            evidence.check_outcome(&arena, &assertions).expect("check"),
            EvidenceCheck::NothingToCheck(NoCheckReason::UncertifiedUnsat)
        );
        assert!(
            elapsed < Duration::from_secs(1),
            "expired deadline must short-circuit, took {elapsed:?}"
        );
    }

    /// ADR-0384 (A4): the deadline is threaded, not merely clamped to zero — with
    /// budget left, the same query still produces its certificate.
    #[test]
    fn ample_deadline_still_produces_the_proof() {
        let (arena, assertions) = unsat_bv_query();
        let deadline = Instant::now().checked_add(Duration::from_secs(60));

        let (evidence, steps) =
            drat_qf_bv_evidence(&arena, &assertions, deadline, None, None).expect("evidence");

        assert!(
            evidence.is_certified(),
            "expected a certificate under budget"
        );
        assert!(evidence.check(&arena, &assertions).expect("check"));
        assert!(
            steps
                .iter()
                .any(|step| step.id == TrustId::SatRefutation && step.certified)
        );
    }

    /// ADR-0384 (A4): a generous `SolverConfig::timeout` must not cost the
    /// certificate — the whole-call budget is threaded, not spent by the
    /// decision phase alone.
    #[test]
    fn produce_qf_bv_evidence_keeps_its_certificate_under_a_generous_timeout() {
        let (arena, assertions) = unsat_bv_query();
        let config = SolverConfig::new().with_timeout(Duration::from_secs(60));

        let report = produce_qf_bv_evidence(&arena, &assertions, &config).expect("evidence");

        assert!(report.evidence.is_certified());
        assert!(report.evidence.check(&arena, &assertions).expect("check"));
    }

    /// ADR-0384 (A5): a consumer can re-check the text front door's own result
    /// against the arena it was produced from — no second parse, so correctness
    /// no longer rests on two parses agreeing on `SymbolId` assignment.
    #[test]
    fn smtlib_evidence_rechecks_without_reparsing() {
        let text = r"(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(assert (= a (bvadd a #x01)))
(check-sat)";

        let produced = produce_evidence_smtlib_with_script(text, &SolverConfig::new())
            .expect("produce evidence");

        assert!(produced.arena_view_faithful);
        assert!(produced.report.evidence.is_certified());
        assert_eq!(
            produced.check_outcome().expect("check"),
            EvidenceCheck::Verified
        );
        // The same subject, reached through the public fields.
        assert!(
            produced
                .report
                .evidence
                .check(&produced.script.arena, &produced.script.assertions)
                .expect("check")
        );
    }

    /// ADR-0384 (A5): the existing signature keeps working and agrees with the
    /// script-returning variant.
    #[test]
    fn smtlib_front_door_signature_is_unchanged() {
        let text = r"(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(assert (= (bvand a #x0f) #x05))
(check-sat)";

        let report = produce_evidence_smtlib(text, &SolverConfig::new()).expect("report");
        let produced =
            produce_evidence_smtlib_with_script(text, &SolverConfig::new()).expect("with script");

        assert_eq!(
            report.evidence.kind_label(),
            produced.report.evidence.kind_label()
        );
        assert_eq!(
            produced.check_outcome().expect("check"),
            EvidenceCheck::Verified
        );
    }

    /// ADR-0384 (A5): handing back the script must not hand back a *vacuous*
    /// check. A string script's flat view is bounded/empty, so a `sat` model
    /// replayed against it would pass having validated nothing (ADR-0061) — the
    /// returned subject reports itself unfaithful instead.
    #[test]
    fn string_script_view_is_not_a_checking_subject() {
        let text = r#"(set-logic QF_S)
(declare-const x String)
(assert (= x (str.++ "a" "b")))
(check-sat)"#;

        let produced = produce_evidence_smtlib_with_script(text, &SolverConfig::new())
            .expect("produce evidence");

        assert!(
            !produced.arena_view_faithful,
            "a string script's flat view is not a checking subject"
        );
        let outcome = produced.check_outcome().expect("check");
        assert!(
            !outcome.is_verified(),
            "the bounded/empty view must never fabricate a verification, got {outcome:?}"
        );
    }

    /// Two forged array-axiom certificates over **satisfiable** queries, each
    /// rejected by exactly one of the two independent stages.
    ///
    /// This family is 30.2% of all certified `unsat` (85 of 281, 2026-08-21).
    /// Its checker used to be `array_axiom_refutation(..).is_some_and(|fresh|
    /// fresh == *cert)` — a determinism check. A recognizer that matched a
    /// satisfiable query matches it identically on the re-run, so the checker
    /// whose entire job is to catch a wrong producer would agree with it.
    ///
    /// Writing the fixtures is what proves the stages are real. Both queries
    /// below are SAT; both certificates are shaped exactly as an honest one; and
    /// each is refused for one specific reason. CLAUDE.md's rule is that a guard
    /// which kills no test is a gap — and staged behind the re-run, both of these
    /// killed nothing, because the equality comparison subsumed them.
    #[test]
    fn a_forged_array_axiom_certificate_over_a_sat_query_is_refused() {
        use crate::array_axiom::{ArrayAxiomKind, ArrayAxiomRefutationCertificate};

        // FIXTURE 1 — the schema claim is a lie.
        // `(not (= (select a i) (select a j)))` is satisfiable (take i != j), and
        // it is not an instance of ANY array axiom. The certificate names the
        // real assertion, is non-degenerate, and claims `ReadOverWrite`.
        // Stage 1 accepts (the assertion does state this disequality) and only
        // stage 2 can refuse it.
        let mut arena = TermArena::new();
        let key = Sort::BitVec(4);
        let value = Sort::BitVec(8);
        let array_sort = Sort::Array {
            index: axeyum_ir::ArraySortKey::BitVec(4),
            element: axeyum_ir::ArraySortKey::BitVec(8),
        };
        let a_sym = arena.declare("a", array_sort).expect("declare a");
        let a = arena.var(a_sym);
        let i_sym = arena.declare("i", key).expect("declare i");
        let i = arena.var(i_sym);
        let j_sym = arena.declare("j", key).expect("declare j");
        let j = arena.var(j_sym);
        let read_i = arena.select(a, i).expect("select");
        let read_j = arena.select(a, j).expect("select");
        let equality = arena.eq(read_i, read_j).expect("eq");
        let assertion = arena.not(equality).expect("not");
        let assertions = vec![assertion];

        let forged = Evidence::UnsatArrayAxiom(ArrayAxiomRefutationCertificate {
            assertion,
            lhs: read_i,
            rhs: read_j,
            kind: ArrayAxiomKind::ReadOverWrite,
        });
        assert!(
            !check_array_axiom_evidence(
                &arena,
                &assertions,
                match &forged {
                    Evidence::UnsatArrayAxiom(c) => c,
                    _ => unreachable!(),
                }
            ),
            "`select(a,i) = select(a,j)` is not a ReadOverWrite instance, and the \
             query it is claimed against is satisfiable at i != j"
        );

        // FIXTURE 2 — the axiom instance is real, but the query never asserts it.
        // `lhs = rhs` here IS a valid read-over-write identity, so `not (lhs =
        // rhs)` would be unsatisfiable — but this query does not assert it. It
        // asserts something else entirely and is satisfiable. Only the
        // `assertions.contains` half of stage 1 stands between this certificate
        // and a "refutation" of a SAT query.
        let v_sym = arena.declare("v", value).expect("declare v");
        let v = arena.var(v_sym);
        let stored = arena.store(a, i, v).expect("store");
        let lhs = arena.select(stored, j).expect("select");
        let same_index = arena.eq(i, j).expect("eq");
        let read_a_j = arena.select(a, j).expect("select");
        let rhs = arena.ite(same_index, v, read_a_j).expect("ite");

        // The certificate names a disequality term that STATES `lhs != rhs`, so
        // stage 1's structural half accepts it. The query does not assert that
        // term — it asserts `i = j` and is satisfiable. Only `assertions.contains`
        // separates the two, which is why the fixture must build the term and
        // then withhold it from the assertion list rather than reusing an
        // unrelated assertion (an earlier draft did, and it was rejected by the
        // wrong guard — it never reached the one under test).
        let forged_equality = arena.eq(lhs, rhs).expect("eq");
        let forged_assertion = arena.not(forged_equality).expect("not");
        let unrelated = arena.eq(i, j).expect("eq");
        let unrelated_assertions = vec![unrelated];
        let forged_instance = ArrayAxiomRefutationCertificate {
            assertion: forged_assertion,
            lhs,
            rhs,
            kind: ArrayAxiomKind::ReadOverWrite,
        };
        assert!(
            crate::array_axiom::assertion_states_disequality(&arena, forged_assertion, lhs, rhs),
            "the fixture must clear stage 1's structural half, or it tests the wrong guard"
        );
        assert!(
            crate::array_axiom::certificate_is_axiom_instance(&arena, &forged_instance),
            "the fixture must be a REAL axiom instance, or it tests the wrong guard"
        );
        assert!(
            !check_array_axiom_evidence(&arena, &unrelated_assertions, &forged_instance),
            "a valid axiom instance the query never asserts refutes nothing"
        );
    }

    /// An Alethe artifact is portable only if EVERY rule in it is one the
    /// external checker checks.
    ///
    /// This is the guard for the overcount half of `portable_artifact`. Before
    /// 2026-08-21 the function answered `Some(Alethe)` for any
    /// `UnsatAletheProof`, so a proof whose array step was named
    /// `read_over_write_same` — which Carcara rejects outright with
    /// `unknown rule`, measured against `references/carcara` at `6624ea80` —
    /// counted toward the published "artifact an external checker can read"
    /// figure. Renaming that one step to Carcara's own `arrays_idx` makes the
    /// same proof `valid`.
    #[test]
    fn an_alethe_proof_naming_a_rule_carcara_lacks_is_not_portable() {
        use axeyum_cnf::{AletheLit, AletheTerm};

        fn row_proof(rule: &str) -> Vec<AletheCommand> {
            let sel = AletheTerm::App(
                "select".to_owned(),
                vec![
                    AletheTerm::App(
                        "store".to_owned(),
                        vec![
                            AletheTerm::Const("a".to_owned()),
                            AletheTerm::Const("i".to_owned()),
                            AletheTerm::Const("v".to_owned()),
                        ],
                    ),
                    AletheTerm::Const("i".to_owned()),
                ],
            );
            let row = AletheTerm::App("=".to_owned(), vec![sel, AletheTerm::Const("v".to_owned())]);
            vec![
                AletheCommand::Assume {
                    id: "h".to_owned(),
                    clause: vec![AletheLit {
                        atom: row.clone(),
                        negated: true,
                    }],
                },
                AletheCommand::Step {
                    id: "s1".to_owned(),
                    clause: vec![AletheLit {
                        atom: row,
                        negated: false,
                    }],
                    rule: rule.to_owned(),
                    premises: Vec::new(),
                    args: Vec::new(),
                },
                AletheCommand::Step {
                    id: "s2".to_owned(),
                    clause: Vec::new(),
                    rule: "resolution".to_owned(),
                    premises: vec!["s1".to_owned(), "h".to_owned()],
                    args: Vec::new(),
                },
            ]
        }

        // Both proofs are accepted by our OWN checker -- that is the point: the
        // in-tree checker cannot tell you whether an outside one can read it.
        let internal = row_proof("read_over_write_same");
        let portable = row_proof("arrays_idx");
        assert_eq!(check_alethe(&internal), Ok(true));
        assert_eq!(check_alethe(&portable), Ok(true));

        assert_eq!(
            Evidence::UnsatAletheProof(internal).portable_artifact(),
            None,
            "`read_over_write_same` is an axeyum-internal rule name; Carcara \
             answers `unknown rule`, so this artifact is not externally checkable"
        );
        assert_eq!(
            Evidence::UnsatAletheProof(portable).portable_artifact(),
            Some(PortableArtifact::Alethe),
            "`arrays_idx` is Carcara's own array rule"
        );
    }

    /// The shipped `QF_ABV` read-over-write-same route must emit a portable
    /// artifact — not merely a checkable one.
    ///
    /// A test that only asserted `check_alethe(&proof) == Ok(true)` would have
    /// passed for the whole period the emitted rule name was one no external
    /// checker knows. This asserts the property that was actually claimed.
    #[test]
    fn the_shipped_qf_abv_row_same_proof_is_portable() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).expect("array var");
        let i = arena.bv_var("i", 4).expect("index var");
        let v = arena.bv_var("v", 8).expect("value var");
        let stored = arena.store(a, i, v).expect("store");
        let sel = arena.select(stored, i).expect("select");
        let eq = arena.eq(sel, v).expect("eq");
        let neq = arena.not(eq).expect("not");

        let proof = crate::prove_qf_abv_unsat_alethe(&arena, &[neq])
            .expect("the ROW-same emitter covers this shape");
        assert_eq!(
            axeyum_cnf::non_carcara_checked_rules(&proof),
            Vec::<String>::new(),
            "the shipped array proof names a rule no external checker has"
        );
        assert_eq!(
            Evidence::UnsatAletheProof(proof).portable_artifact(),
            Some(PortableArtifact::Alethe)
        );
    }

    /// Every certificate that CARRIES a DRAT proof must be reported as portable.
    ///
    /// `portable_artifact`'s wildcard undercounts by construction, and
    /// undercounting is precisely the bug it was written to fix: the published
    /// "8.5% of unsat are externally checkable" was counted from kind LABELS,
    /// while `BoundedIntBlastCertificate` had been carrying a full DRAT
    /// refutation in `bv_proof` the whole time.
    ///
    /// So the source of truth is the source: this reads `evidence.rs` and the
    /// certificate modules, finds every `Evidence` variant whose certificate
    /// type has an `UnsatProof` field, and requires an arm for it. A new
    /// proof-carrying certificate that nobody lists fails here rather than
    /// quietly deflating the metric again.
    ///
    /// It reads files rather than using a trait because a trait would have to be
    /// implemented by hand for each certificate — which is the same act of
    /// remembering, with the same failure mode.
    #[test]
    fn every_proof_carrying_variant_is_listed_as_portable() {
        use std::collections::BTreeSet;
        use std::path::Path;

        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut sources = String::new();
        let mut stack = vec![root.clone()];
        while let Some(dir) = stack.pop() {
            for entry in std::fs::read_dir(&dir).expect("the source tree is readable") {
                let path = entry.expect("a readable entry").path();
                if path.is_dir() {
                    stack.push(path);
                } else if path.extension().is_some_and(|e| e == "rs") {
                    sources.push_str(&std::fs::read_to_string(&path).expect("readable"));
                }
            }
        }
        let evidence = std::fs::read_to_string(root.join("evidence.rs")).expect("readable");

        // Certificate structs with an `UnsatProof`-typed field.
        let mut proof_carrying: BTreeSet<String> = BTreeSet::new();
        for (index, _) in sources.match_indices("pub struct ") {
            let tail = &sources[index..];
            let Some(open) = tail.find('{') else { continue };
            let Some(close) = tail.find("\n}") else {
                continue;
            };
            if close < open {
                continue;
            }
            let name: String = tail["pub struct ".len()..open]
                .split(['<', ' '])
                .next()
                .unwrap_or_default()
                .trim()
                .to_owned();
            if tail[open..close].contains("UnsatProof") && !name.is_empty() {
                proof_carrying.insert(name);
            }
        }
        assert!(
            proof_carrying.len() >= 5,
            "the scan found {} proof-carrying certificates, which is too few to \
             be believable — the parser has drifted, not the code",
            proof_carrying.len()
        );

        // The arms actually listed in `portable_artifact`.
        let listed = evidence
            .split("pub fn portable_artifact")
            .nth(1)
            .and_then(|tail| tail.split("\n    }").next())
            .expect("portable_artifact is present")
            .to_owned();

        for certificate in &proof_carrying {
            // Find the variant that wraps this certificate type, if any.
            let needle = format!("({certificate})");
            let Some(index) = evidence.find(&needle) else {
                continue;
            };
            let head = &evidence[..index];
            let variant = head
                .rsplit(['\n', ' '])
                .find(|token| token.starts_with("Unsat"))
                .unwrap_or_default();
            if variant.is_empty() {
                continue;
            }
            assert!(
                listed.contains(variant),
                "`{variant}` wraps `{certificate}`, which carries an `UnsatProof`, \
                 but `portable_artifact` does not list it — the externally-checkable \
                 count is understated by every instance of this family"
            );
        }
    }

    // ------------------------------------------------------------------
    // Gap #6, continued: three more families whose checker was a re-run of
    // its own producer compared for equality.
    //
    // Every fixture below forges a certificate over a **SATISFIABLE** query.
    // That is the whole method: a determinism check cannot tell an honest
    // certificate from one produced by a recognizer that matched a satisfiable
    // query, because the re-run reproduces the same mistake. A guard that no
    // satisfiable query can exercise is not load-bearing, and per CLAUDE.md
    // deleting each guard below must kill EXACTLY ONE of these tests.
    // ------------------------------------------------------------------

    /// `unsat-nra-even-power`, membership stage. The named conjunct is a
    /// genuine even-power refutation — it just is not in the query. `(> x 0)`
    /// is satisfiable, and without the membership stage the certificate
    /// "refutes" it by exhibiting a contradiction it invented itself.
    #[test]
    fn a_forged_nra_even_power_certificate_naming_an_unasserted_conjunct_is_refused() {
        use crate::nra_even_power::NraEvenPowerRefutationCertificate;
        use axeyum_ir::Rational;

        let mut arena = TermArena::new();
        let x = arena.real_var("x").expect("declare x");
        let zero = arena.real_const(Rational::zero());
        let asserted = arena.real_gt(x, zero).expect("x > 0");
        let square = arena.real_mul(x, x).expect("x * x");
        let unasserted = arena.real_lt(square, zero).expect("x * x < 0");

        let cert = NraEvenPowerRefutationCertificate {
            assertion: unasserted,
            even_power_terms: 1,
            max_even_exponent: 2,
            constant: Rational::zero(),
        };
        // The fixture must CLEAR the shape stage, or it would be testing the
        // wrong guard — the mistake that cost a rewrite on the array-axiom
        // family.
        assert!(
            crate::nra_even_power::certificate_refutes_its_assertion(&arena, &cert),
            "fixture must clear the shape stage so only membership can refuse it"
        );
        assert!(
            !check_nra_even_power_evidence(&arena, &[asserted], &cert),
            "a certificate naming a conjunct the query never asserts must be refused"
        );
    }

    /// `unsat-nra-even-power`, shape stage. `(< (* x y) 0)` is satisfiable at
    /// `x = 1, y = -1`; `x * y` is not an even power of anything. The conjunct
    /// IS asserted, so membership accepts and only the shape stage can refuse.
    #[test]
    fn a_forged_nra_even_power_certificate_over_a_mixed_product_is_refused() {
        use crate::nra_even_power::NraEvenPowerRefutationCertificate;
        use axeyum_ir::Rational;

        let mut arena = TermArena::new();
        let x = arena.real_var("x").expect("declare x");
        let y = arena.real_var("y").expect("declare y");
        let product = arena.real_mul(x, y).expect("x * y");
        let zero = arena.real_const(Rational::zero());
        let assertion = arena.real_lt(product, zero).expect("x * y < 0");

        let cert = NraEvenPowerRefutationCertificate {
            assertion,
            even_power_terms: 1,
            max_even_exponent: 2,
            constant: Rational::zero(),
        };
        assert!(
            !check_nra_even_power_evidence(&arena, &[assertion], &cert),
            "`x * y < 0` is satisfiable and is not an even-power refutation"
        );
    }

    /// `unsat-finite-domain-pigeonhole`, guard 1. Three pairwise-distinct
    /// values, but one of them is an application of a DIFFERENT function, whose
    /// range is unconstrained by `f`'s two-point domain. Satisfiable.
    #[test]
    fn a_forged_pigeonhole_certificate_counting_a_foreign_application_is_refused() {
        use crate::ufbv_finite::FiniteDomainPigeonholeCertificate;

        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::Bool], Sort::BitVec(8))
            .expect("declare f");
        let g = arena
            .declare_fun("g", &[Sort::Bool], Sort::BitVec(8))
            .expect("declare g");
        let arg1 = arena.declare("p", Sort::Bool).expect("p");
        let arg2 = arena.declare("q", Sort::Bool).expect("q");
        let arg3 = arena.declare("r", Sort::Bool).expect("r");
        let (arg1, arg2, arg3) = (arena.var(arg1), arena.var(arg2), arena.var(arg3));
        let fp = arena.apply(f, &[arg1]).expect("f p");
        let fq = arena.apply(f, &[arg2]).expect("f q");
        let gr = arena.apply(g, &[arg3]).expect("g r");

        let mut assertions = Vec::new();
        for (a, b) in [(fp, fq), (fp, gr), (fq, gr)] {
            let eq = arena.eq(a, b).expect("eq");
            assertions.push(arena.not(eq).expect("not"));
        }

        let cert = FiniteDomainPigeonholeCertificate {
            function: f,
            domain_size: 2,
            applications: vec![fp, fq, gr],
        };
        assert!(
            !check_uf_pigeonhole_evidence(&arena, &assertions, &cert),
            "three distinct values across TWO functions do not over-subscribe \
             either one's domain, and this query is satisfiable"
        );
    }

    /// `unsat-finite-domain-pigeonhole`, guard 2. Three applications of one
    /// function over a two-point domain — but only two of the three
    /// disequalities are asserted, so `f q` and `f r` may coincide. Satisfiable
    /// at `p = false`, `q = r = true`.
    #[test]
    fn a_forged_pigeonhole_certificate_with_an_unasserted_pair_is_refused() {
        use crate::ufbv_finite::FiniteDomainPigeonholeCertificate;

        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::Bool], Sort::BitVec(8))
            .expect("declare f");
        let arg1 = arena.declare("p", Sort::Bool).expect("p");
        let arg2 = arena.declare("q", Sort::Bool).expect("q");
        let arg3 = arena.declare("r", Sort::Bool).expect("r");
        let (arg1, arg2, arg3) = (arena.var(arg1), arena.var(arg2), arena.var(arg3));
        let fp = arena.apply(f, &[arg1]).expect("f p");
        let fq = arena.apply(f, &[arg2]).expect("f q");
        let fr = arena.apply(f, &[arg3]).expect("f r");

        let mut assertions = Vec::new();
        for (a, b) in [(fp, fq), (fp, fr)] {
            let eq = arena.eq(a, b).expect("eq");
            assertions.push(arena.not(eq).expect("not"));
        }

        let cert = FiniteDomainPigeonholeCertificate {
            function: f,
            domain_size: 2,
            applications: vec![fp, fq, fr],
        };
        assert!(
            !check_uf_pigeonhole_evidence(&arena, &assertions, &cert),
            "the query never asserts `f q != f r`, so only two distinct values \
             are required and it is satisfiable"
        );
    }

    /// `unsat-finite-domain-pigeonhole`, guard 3. Every disequality is
    /// asserted and every application is `f`'s — but `f`'s domain is
    /// `BitVec(8)`, 256 points, and the certificate says 2. Satisfiable.
    #[test]
    fn a_forged_pigeonhole_certificate_understating_its_domain_is_refused() {
        use crate::ufbv_finite::FiniteDomainPigeonholeCertificate;

        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .expect("declare f");
        let arg1 = arena.declare("u", Sort::BitVec(8)).expect("u");
        let arg2 = arena.declare("v", Sort::BitVec(8)).expect("v");
        let arg3 = arena.declare("w", Sort::BitVec(8)).expect("w");
        let (arg1, arg2, arg3) = (arena.var(arg1), arena.var(arg2), arena.var(arg3));
        let fu = arena.apply(f, &[arg1]).expect("f u");
        let fv = arena.apply(f, &[arg2]).expect("f v");
        let fw = arena.apply(f, &[arg3]).expect("f w");

        let mut assertions = Vec::new();
        for (a, b) in [(fu, fv), (fu, fw), (fv, fw)] {
            let eq = arena.eq(a, b).expect("eq");
            assertions.push(arena.not(eq).expect("not"));
        }

        let cert = FiniteDomainPigeonholeCertificate {
            function: f,
            // A LIE: the real cardinality is 2^8 = 256.
            domain_size: 2,
            applications: vec![fu, fv, fw],
        };
        assert!(
            !check_uf_pigeonhole_evidence(&arena, &assertions, &cert),
            "three distinct values of a 256-point-domain function is satisfiable; \
             the domain cardinality must be recomputed, never read from the \
             certificate"
        );
    }

    /// `unsat-finite-domain-pigeonhole`, guard 4. Two distinct values over a
    /// two-point domain is an exact fit, not an over-subscription. Satisfiable.
    #[test]
    fn a_forged_pigeonhole_certificate_at_an_exact_domain_fit_is_refused() {
        use crate::ufbv_finite::FiniteDomainPigeonholeCertificate;

        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::Bool], Sort::BitVec(8))
            .expect("declare f");
        let arg1 = arena.declare("p", Sort::Bool).expect("p");
        let arg2 = arena.declare("q", Sort::Bool).expect("q");
        let (arg1, arg2) = (arena.var(arg1), arena.var(arg2));
        let fp = arena.apply(f, &[arg1]).expect("f p");
        let fq = arena.apply(f, &[arg2]).expect("f q");
        let eq = arena.eq(fp, fq).expect("eq");
        let assertions = vec![arena.not(eq).expect("not")];

        let cert = FiniteDomainPigeonholeCertificate {
            function: f,
            domain_size: 2,
            applications: vec![fp, fq],
        };
        assert!(
            !check_uf_pigeonhole_evidence(&arena, &assertions, &cert),
            "two distinct values over a two-point domain is satisfiable — the \
             pigeonhole inequality must be STRICT"
        );
    }

    /// A one-bit-index array pair and its two concrete reads, shared by the
    /// finite-array extensionality fixtures below.
    fn finite_array_ext_fixture(
        arena: &mut TermArena,
    ) -> (TermId, TermId, [TermId; 2], [TermId; 2]) {
        let array_sort = Sort::Array {
            index: axeyum_ir::ArraySortKey::BitVec(1),
            element: axeyum_ir::ArraySortKey::BitVec(8),
        };
        let a = arena.declare("a", array_sort).expect("a");
        let b = arena.declare("b", array_sort).expect("b");
        let (a, b) = (arena.var(a), arena.var(b));
        let mut a_reads = [a; 2];
        let mut b_reads = [b; 2];
        for value in 0..2u128 {
            let index = arena.bv_const(1, value).expect("index");
            a_reads[value as usize] = arena.select(a, index).expect("select a");
            b_reads[value as usize] = arena.select(b, index).expect("select b");
        }
        (a, b, a_reads, b_reads)
    }

    fn finite_array_read(
        arena: &mut TermArena,
        lhs_read: TermId,
        rhs_read: TermId,
        index_value: u128,
    ) -> crate::array_finite::FiniteArrayReadEquality {
        crate::array_finite::FiniteArrayReadEquality {
            equality: arena.eq(lhs_read, rhs_read).expect("read equality"),
            lhs_read,
            rhs_read,
            index_value,
        }
    }

    /// `unsat-finite-array-extensionality`, coverage guard (count half). One
    /// index of a two-point domain is left uncovered, so the arrays may differ
    /// exactly there. Satisfiable.
    #[test]
    fn a_forged_finite_array_extensionality_certificate_missing_an_index_is_refused() {
        use crate::array_finite::FiniteArrayExtensionalityCertificate;

        let mut arena = TermArena::new();
        let (a, b, a_reads, b_reads) = finite_array_ext_fixture(&mut arena);
        let read0 = finite_array_read(&mut arena, a_reads[0], b_reads[0], 0);
        let array_eq = arena.eq(a, b).expect("a = b");
        let diseq = arena.not(array_eq).expect("not");
        let assertions = vec![diseq, read0.equality];

        let cert = FiniteArrayExtensionalityCertificate {
            lhs_array: a,
            rhs_array: b,
            index_width: 1,
            read_equalities: vec![read0],
        };
        assert!(
            !check_finite_array_extensionality_evidence(&arena, &assertions, &cert),
            "one of two indices is uncovered, so the arrays may differ there"
        );
    }

    /// `unsat-finite-array-extensionality`, coverage guard (position half). The
    /// certificate carries the right NUMBER of read equalities — by listing the
    /// same index twice. Index 1 is still uncovered. Satisfiable.
    #[test]
    fn a_forged_finite_array_extensionality_certificate_repeating_an_index_is_refused() {
        use crate::array_finite::FiniteArrayExtensionalityCertificate;

        let mut arena = TermArena::new();
        let (a, b, a_reads, b_reads) = finite_array_ext_fixture(&mut arena);
        let read0 = finite_array_read(&mut arena, a_reads[0], b_reads[0], 0);
        let array_eq = arena.eq(a, b).expect("a = b");
        let diseq = arena.not(array_eq).expect("not");
        let assertions = vec![diseq, read0.equality];

        let cert = FiniteArrayExtensionalityCertificate {
            lhs_array: a,
            rhs_array: b,
            index_width: 1,
            read_equalities: vec![read0.clone(), read0],
        };
        assert!(
            !check_finite_array_extensionality_evidence(&arena, &assertions, &cert),
            "two read equalities at the SAME index cover a two-point domain no \
             better than one does"
        );
    }

    /// `unsat-finite-array-extensionality`, membership guard. Both read
    /// equalities are genuine terms the query never asserts; it says only that
    /// the arrays differ, which is satisfiable.
    #[test]
    fn a_forged_finite_array_extensionality_certificate_with_unasserted_reads_is_refused() {
        use crate::array_finite::FiniteArrayExtensionalityCertificate;

        let mut arena = TermArena::new();
        let (a, b, a_reads, b_reads) = finite_array_ext_fixture(&mut arena);
        let read0 = finite_array_read(&mut arena, a_reads[0], b_reads[0], 0);
        let read1 = finite_array_read(&mut arena, a_reads[1], b_reads[1], 1);
        let array_eq = arena.eq(a, b).expect("a = b");
        let assertions = vec![arena.not(array_eq).expect("not")];

        let cert = FiniteArrayExtensionalityCertificate {
            lhs_array: a,
            rhs_array: b,
            index_width: 1,
            read_equalities: vec![read0, read1],
        };
        assert!(
            !check_finite_array_extensionality_evidence(&arena, &assertions, &cert),
            "the query asserts none of the pointwise equalities; a certificate \
             may not supply its own premises"
        );
    }

    /// `unsat-finite-array-extensionality`, shape guard. The conjunct named for
    /// index 1 is asserted, but it equates `a[1]` with `b[0]` — a real
    /// constraint that says nothing about `b[1]`. Satisfiable.
    #[test]
    fn a_forged_finite_array_extensionality_certificate_with_a_crossed_read_is_refused() {
        use crate::array_finite::FiniteArrayExtensionalityCertificate;

        let mut arena = TermArena::new();
        let (a, b, a_reads, b_reads) = finite_array_ext_fixture(&mut arena);
        let read0 = finite_array_read(&mut arena, a_reads[0], b_reads[0], 0);
        // `a[1] = b[0]`, recorded as if it were the index-1 read equality.
        let crossed = finite_array_read(&mut arena, a_reads[1], b_reads[0], 1);
        let array_eq = arena.eq(a, b).expect("a = b");
        let diseq = arena.not(array_eq).expect("not");
        let assertions = vec![diseq, read0.equality, crossed.equality];

        let cert = FiniteArrayExtensionalityCertificate {
            lhs_array: a,
            rhs_array: b,
            index_width: 1,
            read_equalities: vec![read0, crossed],
        };
        assert!(
            !check_finite_array_extensionality_evidence(&arena, &assertions, &cert),
            "`a[1] = b[0]` is not the index-1 pointwise equality and leaves \
             `b[1]` free"
        );
    }

    /// `unsat-finite-array-extensionality`, disequality guard. Every pointwise
    /// equality is asserted and nothing says the arrays differ, so `a = b`
    /// satisfies the query.
    #[test]
    fn a_forged_finite_array_extensionality_certificate_without_the_disequality_is_refused() {
        use crate::array_finite::FiniteArrayExtensionalityCertificate;

        let mut arena = TermArena::new();
        let (a, b, a_reads, b_reads) = finite_array_ext_fixture(&mut arena);
        let read0 = finite_array_read(&mut arena, a_reads[0], b_reads[0], 0);
        let read1 = finite_array_read(&mut arena, a_reads[1], b_reads[1], 1);
        let assertions = vec![read0.equality, read1.equality];

        let cert = FiniteArrayExtensionalityCertificate {
            lhs_array: a,
            rhs_array: b,
            index_width: 1,
            read_equalities: vec![read0, read1],
        };
        assert!(
            !check_finite_array_extensionality_evidence(&arena, &assertions, &cert),
            "nothing asserts the arrays differ, so `a = b` satisfies the query"
        );
    }
}
