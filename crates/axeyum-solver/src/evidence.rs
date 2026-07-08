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
//!   DRAT); `check` re-parses and re-runs the trusted [`axeyum_cnf::check_drat`]
//!   kernel. A `None` proof means the result came from the (lower-assurance)
//!   adapter without a DRAT certificate, and is documented as such.
//! - `QF_LRA` `unsat` carries a [`FarkasCertificate`]; `check` re-runs the
//!   independent [`FarkasCertificate::verify`] (the exact-arithmetic dual of the
//!   DRAT route).
//! - Boolean-structured pure-real `unsat` carries an [`LraDpllRefutation`];
//!   `check` re-runs [`LraDpllRefutation::verify`].
//! - Boolean-structured linear-arithmetic `unsat` carries an
//!   [`ArithDpllRefutation`]; `check` re-runs [`ArithDpllRefutation::verify`].
//! - `unknown` carries the reason and checks vacuously.
//!
//! [`produce_qf_bv_evidence`], [`produce_lra_evidence`], and
//! [`produce_lra_dpll_evidence`] run the per-theory pipelines, and
//! [`produce_evidence`] is the unified front door that routes any supported query
//! to the producer with the strongest available certificate (mirroring
//! [`crate::solve`]).

use std::collections::BTreeSet;
use std::time::{Duration, Instant};

use axeyum_cnf::{AletheCommand, check_alethe, check_drat, parse_dimacs, parse_drat};
use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode, TermStats, Value, eval};

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
use crate::nra_even_power::NraEvenPowerRefutationCertificate;
use crate::nra_real_root::{self, SosCertificate};
use crate::proof::{UnsatProof, UnsatProofOutcome, export_qf_bv_unsat_proof};
use crate::quant_finite_cert::{
    GuardedUniversalForm, check_alethe_lra_guarded_inst_against, guarded_universal_form,
    guarded_universal_form_uf, prove_finite_int_quant_unsat_alethe,
    prove_finite_int_quant_unsat_uf_alethe,
};
use crate::sat_bv_backend::SatBvBackend;
use crate::set_cardinality::SetCardinalityRefutationCertificate;
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
    /// Unsatisfiable (`NRA`): the query asserts a syntactic sum of even powers
    /// plus a nonnegative rational constant is strictly negative. The checker
    /// re-scans the original assertions and re-matches the exact nonnegativity
    /// shape before accepting.
    UnsatNraEvenPower(NraEvenPowerRefutationCertificate),
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
    /// Undecided, with the classified reason.
    Unknown(UnknownReason),
}

impl Evidence {
    /// Stable short label for this evidence variant.
    ///
    /// These labels are intended for SDK/UI summaries and artifact metadata.
    /// They are deliberately independent of Rust `Debug` formatting.
    #[must_use]
    pub const fn kind_label(&self) -> &'static str {
        match self {
            Evidence::Sat(_) => "sat-model",
            Evidence::Unsat(_) => "unsat-drat",
            Evidence::UnsatAletheProof(_) => "unsat-alethe",
            Evidence::UnsatArithAletheProof(_) => "unsat-arith-alethe",
            Evidence::UnsatGuardedQuantAletheProof { .. } => "unsat-guarded-quant-alethe",
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
            Evidence::UnsatNraEvenPower(_) => "unsat-nra-even-power",
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
            Evidence::Unknown(_) => "unknown",
        }
    }

    /// Independently re-validates this evidence against the original
    /// `assertions`. Returns `true` when the evidence holds up.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Backend`] if a `sat` replay evaluates to a
    /// non-Boolean (an internal invariant violation) or a stored certificate
    /// fails to re-parse.
    #[allow(clippy::too_many_lines)]
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
                | Evidence::UnsatGuardedQuantAletheProof { .. }
                | Evidence::UnsatTermLevel { .. }
                | Evidence::UnsatFiniteDomainEnum { .. }
                | Evidence::UnsatBvDefinedEnum(_)
                | Evidence::UnsatBvForallNonconstant(_)
                | Evidence::UnsatBvUfLocal(_)
                | Evidence::UnsatSetCardinality(_)
                | Evidence::UnsatFarkas(_)
                | Evidence::UnsatLraDpll(_)
                | Evidence::UnsatArithDpll(_)
                | Evidence::UnsatSos { .. }
                | Evidence::UnsatNraEvenPower(_)
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

fn check_uf_pigeonhole_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &FiniteDomainPigeonholeCertificate,
) -> bool {
    crate::ufbv_finite::finite_domain_pigeonhole_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
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

fn check_finite_array_extensionality_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &FiniteArrayExtensionalityCertificate,
) -> bool {
    crate::array_finite::finite_array_extensionality_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
}

fn check_bool_array_read_collapse_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &BoolArrayReadCollapseCertificate,
) -> bool {
    cert.recheck(arena, assertions)
}

fn check_nra_even_power_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &NraEvenPowerRefutationCertificate,
) -> bool {
    crate::nra_even_power::nra_even_power_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == *cert)
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

fn check_array_axiom_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &ArrayAxiomRefutationCertificate,
) -> bool {
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
pub fn produce_qf_bv_evidence(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<EvidenceReport, SolverError> {
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
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text, or any [`SolverError`]
/// from the chosen engine.
pub fn produce_evidence_smtlib(
    input: &str,
    config: &SolverConfig,
) -> Result<EvidenceReport, SolverError> {
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
        return Ok(report);
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
        CheckResult::Unsat => string_unsat_evidence(&mut script, config),
        CheckResult::Unknown(reason) => Evidence::Unknown(reason),
    };
    Ok(EvidenceReport {
        evidence,
        provenance,
        trusted_steps: Vec::new(),
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
/// 3. Otherwise (concat/length conflict, or a reconstruction/cap decline) a correct
///    bare-but-sound [`Evidence::Unsat(None)`](Evidence::Unsat).
///
/// The verdict is never changed — this is a pure evidence upgrade over the object the
/// route already decided. Each certificate independently re-checks; a decline is a
/// clean fall-through to the next class, never a fabricated certificate.
fn string_unsat_evidence(script: &mut axeyum_smtlib::Script, config: &SolverConfig) -> Evidence {
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
    // (3) No transferable certificate yet: the correct, honestly-uncertified verdict.
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
/// 1. [`crate::prove_qf_abv_unsat_alethe`] — the array read-over-write-same /
///    extensionality DIRECT cert (proves the conflict via the array axiom);
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
        | Evidence::UnsatGuardedQuantAletheProof { .. }
        | Evidence::UnsatTermLevel { .. }
        | Evidence::UnsatFiniteDomainEnum { .. }
        | Evidence::UnsatBvDefinedEnum(_)
        | Evidence::UnsatBvForallNonconstant(_)
        | Evidence::UnsatBvUfLocal(_)
        | Evidence::UnsatSetCardinality(_)
        | Evidence::UnsatFarkas(_)
        | Evidence::UnsatLraDpll(_)
        | Evidence::UnsatArithDpll(_)
        | Evidence::UnsatSos { .. }
        | Evidence::UnsatNraEvenPower(_)
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
        | Evidence::UnsatWordClash(_) => {
            if !report.evidence.check(arena, &query)? {
                return Err(SolverError::Backend(
                    "prove: refutation of the negated goal failed its own check".to_owned(),
                ));
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
            Sort::BitVec(_) | Sort::Float { .. } => has_bitvec = true,
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
