//! The backend trait, results, configuration, and capabilities.

use std::time::Duration;

use axeyum_bv::RangeDemandPolicy;
use axeyum_ir::{TermArena, TermId};
use axeyum_query::Query;

use crate::model::Model;

/// Outcome of a satisfiability check.
///
/// `Unknown` is a first-class result, never an error (mission rule): it is
/// the correct answer for timeouts, resource limits, and incomplete
/// procedures.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckResult {
    /// The assertions are satisfiable. Ground symbols map to values (backend
    /// model completion fills unconstrained symbols); restricted
    /// infinite-domain quantified results additionally carry checked Skolem or
    /// finite-profile UF-model certificates. Use `check_model` for canonical
    /// replay when the `full` feature is enabled.
    Sat(Model),
    /// The assertions are unsatisfiable.
    Unsat,
    /// The backend could not decide; the payload says why, structurally,
    /// so "budget exhausted" can never be misread as "unsat".
    Unknown(UnknownReason),
}

/// Why a check came back undecided.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct UnknownReason {
    /// Classified cause.
    pub kind: UnknownKind,
    /// Backend-specific detail (for example Z3's reason string).
    pub detail: String,
}

/// Classified causes of an `Unknown` result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum UnknownKind {
    /// Wall-clock budget exhausted.
    Timeout,
    /// Deterministic resource budget (e.g. Z3 `rlimit`) exhausted.
    ResourceLimit,
    /// Memory budget exhausted.
    MemoryLimit,
    /// Translation node budget exceeded; the query was never submitted.
    NodeBudget,
    /// CNF size budget exceeded; the query was lowered but not submitted to
    /// the SAT adapter.
    EncodingBudget,
    /// The procedure is incomplete for this query.
    Incomplete,
    /// Unclassified backend reason.
    Other,
}

// `SolverError` now lives in the leaf module `crate::error` and is re-exported
// here, so every existing `use crate::backend::SolverError` keeps working. It
// moved to break `backend -> model -> quant_sat_certificates -> proof -> backend`:
// `proof` was in that cycle only because it names this type. See `crate::error`.
pub use crate::error::SolverError;

/// Cold bit-vector lowering strategy.
///
/// The two sparse modes are separate, off-by-default experiments. Encoding the
/// selection as one enum makes simultaneous dense-demand and range-demand
/// lowering unrepresentable.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum BitLoweringMode {
    /// Lower every reachable bit with the ordinary eager pipeline.
    #[default]
    Eager,
    /// Force ADR-0157's dense exact demand-sliced lowering.
    DemandSliced,
    /// Run ADR-0158's admission-controlled range-demand lowering.
    RangeSliced(RangeDemandPolicy),
}

/// Per-query configuration.
///
/// Backends are one-shot for now, so budgets are the cancellation
/// mechanism; a cooperative interrupt flag arrives with long-lived solver
/// instances (incrementality note). Every budget exhaustion surfaces as
/// [`CheckResult::Unknown`] with a classified reason, never a hang.
///
/// The several `bool` fields are independent, off-by-default opt-in performance
/// /assurance levers (DRAT proof, CNF inprocessing, word-level preprocessing, the
/// CDCL(XOR) fallback), not a state machine — a flat config of toggles is the
/// intended shape, so the `struct_excessive_bools` lint is allowed here.
#[derive(Debug, Clone)]
#[allow(clippy::struct_excessive_bools)]
pub struct SolverConfig {
    /// Wall-clock budget for the check; `None` means no limit.
    pub timeout: Option<Duration>,
    /// Deterministic backend search budget; reproducible across machines and
    /// preferred for bisecting blowups.
    ///
    /// Units are backend-specific: Z3 `rlimit` units, `BatSat`
    /// `within_budget` progress checks on the cold SAT-BV path, or conflicts in
    /// the proof-producing native CDCL core. Artifacts must record the backend
    /// and unit; numeric values are not cross-backend work-equivalent.
    pub resource_limit: Option<u64>,
    /// Memory budget in megabytes. Caveat: Z3 applies this process-wide.
    pub memory_limit_mb: Option<u64>,
    /// Maximum DAG nodes the backend may translate; larger queries return
    /// [`UnknownKind::NodeBudget`] without being submitted (admission
    /// control, query-cost-control note).
    pub node_budget: Option<u64>,
    /// Maximum CNF variables the backend may submit to the SAT adapter.
    ///
    /// Larger encodings return [`UnknownKind::EncodingBudget`] before SAT
    /// solving starts.
    pub cnf_variable_budget: Option<u64>,
    /// Maximum CNF clauses the backend may submit to the SAT adapter.
    ///
    /// Larger encodings return [`UnknownKind::EncodingBudget`] before SAT
    /// solving starts.
    pub cnf_clause_budget: Option<u64>,
    /// On the SAT-BV path, accept `unsat` only when it is backed by a verified
    /// DRAT proof (ADR-0011/0012). The current primary path selects the
    /// proof-producing native CDCL core and checks its proof inline in the same
    /// solve. A compatibility path that arrives with an unchecked adapter result
    /// independently re-derives and verifies the proof. Lack of a checked proof
    /// fails closed to [`CheckResult::Unknown`]; a fallback disagreement or
    /// malformed proof becomes a [`SolverError::Backend`] soundness alarm. The
    /// proof core is a reference, not scalable, so this is for small instances /
    /// high-assurance checks.
    pub prove_unsat: bool,
    /// When set, the bit-blasting BV backend runs CNF inprocessing
    /// (subsumption + bounded variable elimination) on the Tseitin formula
    /// before handing it to the SAT adapter.
    ///
    /// The transforms are model-preserving (subsumption) and equisatisfiable
    /// (BVE, lifted back through its reconstruction stack), and every `sat`
    /// result is still replay-checked against the original terms, so this is a
    /// sound, off-by-default performance lever (Track 1, P1.1). Defaults to
    /// `false` so the recorded baselines reflect the un-inprocessed encoding.
    pub cnf_inprocessing: bool,
    /// When set (and `cnf_inprocessing` is also on), the bit-blasting BV backend
    /// runs a clause-vivification pass ([`axeyum_cnf::vivify_within`]) between the
    /// subsumption and `BVE` inprocessing passes.
    ///
    /// Vivification is **model-preserving** (same satisfying assignments, same
    /// `variable_count` — no reconstruction trail), so the model-lift stack is
    /// unchanged and every `sat` result is still replay-checked against the
    /// original terms; it only strengthens (shrinks) clauses, never changing the
    /// verdict. A no-op unless `cnf_inprocessing` is set. Off by default so
    /// recorded baselines reflect the un-vivified inprocessing path.
    ///
    /// Proof accounting: in `prove_unsat` mode the vivify pass's `DRAT` is
    /// *step-checked* (RUP-verified by [`axeyum_cnf::check_drat`] against the
    /// formula it acted on, matching `vivify`'s own contract) but is **not yet
    /// composed** into the final end-to-end solve proof — the same accounting tier
    /// as the subsumption and `BVE` passes, whose inprocessing `DRAT` is likewise
    /// not threaded into the solve proof (the backend relies on an
    /// equisatisfiability meta-argument). Full `DRAT` composition is a separate,
    /// larger task.
    pub cnf_vivify: bool,
    /// When set, the full-profile `check_auto`/`solve` entry points run the
    /// denotation-preserving canonicalizer over the assertions before dispatch
    /// (Track 1, P1.2 word-level preprocessing). It is symbol-preserving — no
    /// variables are eliminated — so the returned `sat` model is unchanged and
    /// still satisfies the original assertions; it normalizes commutative-operand
    /// order (so e.g. `(= (bvmul a b) (bvmul b a))` folds to `true` with no
    /// bit-blasting) and applies the identity/constant-fold rules. On by default:
    /// the canonicalizer is a measured net win and preserves original-term model
    /// replay. Recorded artifacts must still retain the complete configuration.
    pub preprocess: bool,
    /// Computes the observational structural bit-demand profile during
    /// SAT-BV lowering.
    ///
    /// This can cost more than the production lowering itself on real lifter
    /// formulas. It never changes the circuit or verdict and is off by default;
    /// enable it only for relevant-bit diagnostics (ADR-0143).
    pub profile_bit_demand: bool,
    /// Collects detailed AIG-to-CNF literal-canonicalization and clause-index
    /// attribution on the cold SAT-BV path.
    ///
    /// This selects a separately monomorphized encoder; the ordinary encoder
    /// has no profiling storage or counter updates. It never changes the CNF or
    /// verdict and is off by default (ADR-0259).
    pub profile_cnf_construction: bool,
    /// Selects the cold bit-vector lowering strategy.
    ///
    /// [`BitLoweringMode::DemandSliced`] propagates live output-bit demand
    /// backward and materializes only demanded term and symbol bits.
    /// [`BitLoweringMode::RangeSliced`] first applies deterministic admission
    /// thresholds and a work budget, falling back to eager lowering when the
    /// sparse plan is not worthwhile. Both modes retain deterministic omitted-bit
    /// completion and mandatory original-term model replay. The default is
    /// [`BitLoweringMode::Eager`]. A sparse mode's complete structural-demand
    /// telemetry supersedes [`Self::profile_bit_demand`].
    pub bit_lowering_mode: BitLoweringMode,
    /// Enables bounded positive internal AND-tree half flattening in the warm
    /// incremental CNF encoder (ADR-0173's selected GQ5 experiment).
    ///
    /// Admission requires fresh bypassed halves, bounded traversal, and an
    /// exact immediate clause reduction. Bypassed helpers remain available for
    /// later ordinary definition emission, and model lifting still reconstructs
    /// AIG nodes from inputs before original-term replay. Off by default until
    /// the repeated native-client gate accepts it.
    pub incremental_positive_and_flattening: bool,
    /// When set, the bit-blasting BV backend may fall back to the CDCL(XOR)
    /// search core ([`axeyum_cnf::solve_with_xor_cdcl`]) after the primary SAT
    /// solve returns `unknown` (timeout/budget) on an XOR-structured formula
    /// (ADR-0035, the multiplier-equivalence wall). The primary engine is the
    /// native CDCL core (ADR-1703); the trigger is its `unknown`, exactly as it
    /// was the retired adapter's.
    ///
    /// A fallback `unsat` is a **trusted** result (search-only Gaussian
    /// reasoning carries no DRAT proof — it is not RUP) and is recorded as the
    /// full-profile `TrustId::XorGaussian` ledger hole. A fallback `sat` carries no
    /// trust cost: its model is replayed against the original terms exactly like
    /// the primary path, and a replay failure falls through to `unknown` (never a
    /// wrong `sat`). Off by default so recorded baselines and existing behavior
    /// are unchanged.
    pub xor_cdcl_fallback: bool,

    /// Use the lazy abstraction-refinement (CEGAR) bit-blasting strategy (P2.1,
    /// ADR-0019) for the quantifier-free path instead of eager bit-blasting:
    /// abstract heavy BV gadgets (`bvmul`/`bvudiv`/…) by fresh variables, solve
    /// the small abstraction, and refine only the operations a candidate model
    /// violates — sidestepping the eager multiplier "mountain" on problems whose
    /// heavy ops are incidental to the verdict. Sound (over-approximation for
    /// `unsat`; every `sat` replays) and a safe no-op when no heavy ops are
    /// present. Off by default so recorded baselines are unchanged.
    pub lazy_bv: bool,

    /// **Deprecated no-op, kept for API compatibility (ADR-1703).**
    ///
    /// The in-tree proof-producing CDCL core
    /// ([`axeyum_cnf::solve_with_drat_proof_within`]) is now the primary SAT
    /// search on every path, so there is nothing left for this flag to select.
    /// It is read by nobody: [`crate::SatBvBackend`] dispatches to the native
    /// core unconditionally. Setting it either way changes no verdict, no
    /// timing, and no artifact except the recorded config itself.
    ///
    /// It survives only because `axeyum-py`, `axeyum-bench` and `axeyum-verify`
    /// name the field; slice 2 of ADR-1703 removes it along with the adapter.
    pub native_cdcl: bool,

    /// Extend lazy bit-blasting (`lazy_bv`) to also abstract `ite` — the
    /// dominant operator on control-heavy `QF_BV` (software/protocol verification),
    /// where the public measurement showed there are no heavy arithmetic gadgets
    /// to abstract but hundreds of thousands of `ite`s. Abstracting a BV-sorted
    /// `ite` by a fresh variable is the same sound over-approximation (refining
    /// `fresh == ite(c,t,e)` only when a model violates it), pruning the abstracted
    /// branches from the eager circuit. Only meaningful with `lazy_bv`; off by
    /// default (experimental, gated on a measured win).
    pub lazy_bv_abstract_ite: bool,

    /// Observability hook for the proof-producing DRAT search
    /// ([`axeyum_cnf::ProofSearchProgress`]): when set, periodic
    /// `ProofSearchProgress` snapshots are sent down `sink` while the
    /// certificate-producing SAT search on the `QF_BV` path runs (see
    /// `crate::proof::export_qf_bv_unsat_proof_with_progress`, reached from
    /// `produce_qf_bv_evidence`'s DRAT-certificate route).
    ///
    /// `None` by default, matching every other assurance/perf lever here: a
    /// progress sink is *output only* — nothing reads it back — so installing
    /// one cannot change a verdict or the emitted DRAT proof; it can only
    /// change how often, and to where, a snapshot is reported.
    pub proof_progress: Option<ProofProgress>,

    /// Observability and bounding for the CHECKING stage that follows the
    /// search above on a `QF_BV` `unsat` (`axeyum_cnf::check_drat` then, if
    /// that verifies, `axeyum_cnf::elaborate_drat_to_lrat` —
    /// [`crate::proof::CheckingProgress`] / [`crate::proof::CheckBudget`]).
    ///
    /// `proof_progress` above watches the SEARCH; this watches what runs
    /// *after* the search returns `unsat`, which had no bound and no
    /// observability at all until this field existed — the incident that
    /// motivates it is a 24.2 s search followed by a ~6 h checking pass with
    /// zero output on `neg-fp16-add-monotone-rne.smt2`. `None` by default:
    /// installing a sink or a bound here can only change whether/when
    /// checking gives up early (reported as `Inconclusive`, never as a
    /// timeout-shaped `Proved`), never what a completed check accepts.
    pub check_progress: Option<CheckProgress>,
}

/// A progress sink installed on [`SolverConfig::proof_progress`]. `sink` is a
/// channel [`Sender`](std::sync::mpsc::Sender) rather than a boxed closure so
/// [`SolverConfig`] keeps its ordinary `Clone`/`Debug` derives (a channel
/// sender is `Clone` and `Debug` unconditionally, without requiring the
/// message type to be either) and so a caller can drain snapshots from a
/// different thread than the one running the search — exactly the shape
/// `smtcomp_cli`'s watchdog-timeout worker thread needs.
#[derive(Debug, Clone)]
pub struct ProofProgress {
    /// Conflict-count cadence between snapshots (forwarded to
    /// `axeyum_cnf::solve_with_drat_proof_with_limits_and_progress`).
    pub interval: usize,
    /// Where snapshots are sent. A closed receiver is not an error: a send
    /// failure is silently dropped (see the call site), since a progress
    /// report reaching nobody must never abort or alter the search.
    pub sink: std::sync::mpsc::Sender<axeyum_cnf::ProofSearchProgress>,
}

impl ProofProgress {
    /// Builds a progress config with the given conflict-count `interval`
    /// (clamped to at least 1 by the underlying search) and channel `sink`.
    #[must_use]
    pub fn new(
        interval: usize,
        sink: std::sync::mpsc::Sender<axeyum_cnf::ProofSearchProgress>,
    ) -> Self {
        Self { interval, sink }
    }
}

/// A progress sink installed on [`SolverConfig::check_progress`], plus the
/// wall-clock deadline and step budget the checking stage should honor.
/// Mirrors [`ProofProgress`]'s channel-based design so the same
/// `smtcomp_cli`-style watchdog thread can drain it, and additionally carries
/// the bound itself: unlike the search (whose deadline lives on
/// [`SolverConfig::timeout`] and is threaded through separately), checking has
/// no other budget field to read, so this is the only place a caller can hand
/// one to it.
#[derive(Debug, Clone)]
pub struct CheckProgress {
    /// Step cadence between snapshots (forwarded to
    /// `axeyum_cnf::check_drat_with_limits_and_progress` /
    /// `axeyum_cnf::elaborate_drat_to_lrat_with_limits_and_progress`).
    pub interval: usize,
    /// Optional step budget for the checking stage. `None` means checking is
    /// bounded only by whatever wall-clock deadline the caller derives from
    /// [`SolverConfig::timeout`] (see `crate::evidence::produce_qf_bv_evidence`),
    /// which itself is `None` (unbounded) unless the caller set a timeout.
    pub max_steps: Option<usize>,
    /// Where snapshots are sent. A closed receiver is not an error: a send
    /// failure is silently dropped, since a progress report reaching nobody
    /// must never abort or alter checking.
    pub sink: std::sync::mpsc::Sender<crate::proof::CheckingProgress>,
}

impl CheckProgress {
    /// Builds a checking-progress config with the given step-count `interval`
    /// (clamped to at least 1 by the underlying checker), an optional step
    /// budget, and channel `sink`.
    #[must_use]
    pub fn new(
        interval: usize,
        max_steps: Option<usize>,
        sink: std::sync::mpsc::Sender<crate::proof::CheckingProgress>,
    ) -> Self {
        Self {
            interval,
            max_steps,
            sink,
        }
    }
}

impl Default for SolverConfig {
    /// All assurance/perf levers off and no budgets, **except** word-level
    /// `preprocess`, which defaults **on** (ADR-0037/0034): denotation-preserving
    /// reduction before dispatch is a measured net win on the public corpus
    /// (`+preprocess`: 4/113 @3s, 7/113 @20s vs eager 2/3; `DISAGREE=0`) and
    /// model-sound + replay-checked, so it is safe as the default. Other levers stay
    /// off so baselines/behaviour are otherwise unchanged.
    fn default() -> Self {
        Self {
            timeout: None,
            resource_limit: None,
            memory_limit_mb: None,
            node_budget: None,
            cnf_variable_budget: None,
            cnf_clause_budget: None,
            prove_unsat: false,
            cnf_inprocessing: false,
            cnf_vivify: false,
            preprocess: true,
            profile_bit_demand: false,
            profile_cnf_construction: false,
            bit_lowering_mode: BitLoweringMode::Eager,
            incremental_positive_and_flattening: false,
            xor_cdcl_fallback: false,
            lazy_bv: false,
            lazy_bv_abstract_ite: false,
            native_cdcl: false,
            proof_progress: None,
            check_progress: None,
        }
    }
}

impl SolverConfig {
    /// An empty configuration with no budgets (same as `Default`).
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets the wall-clock timeout.
    #[must_use]
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// Sets the deterministic backend search budget.
    ///
    /// See [`SolverConfig::resource_limit`] for backend-specific units.
    #[must_use]
    pub fn with_resource_limit(mut self, limit: u64) -> Self {
        self.resource_limit = Some(limit);
        self
    }

    /// Sets the memory budget in megabytes.
    #[must_use]
    pub fn with_memory_limit_mb(mut self, megabytes: u64) -> Self {
        self.memory_limit_mb = Some(megabytes);
        self
    }

    /// Sets the maximum DAG nodes the backend may translate.
    #[must_use]
    pub fn with_node_budget(mut self, nodes: u64) -> Self {
        self.node_budget = Some(nodes);
        self
    }

    /// Sets the maximum CNF variables the backend may submit.
    #[must_use]
    pub fn with_cnf_variable_budget(mut self, variables: u64) -> Self {
        self.cnf_variable_budget = Some(variables);
        self
    }

    /// Sets the maximum CNF clauses the backend may submit.
    #[must_use]
    pub fn with_cnf_clause_budget(mut self, clauses: u64) -> Self {
        self.cnf_clause_budget = Some(clauses);
        self
    }

    /// Enables independent DRAT proof verification of `unsat` results.
    #[must_use]
    pub fn with_prove_unsat(mut self, prove_unsat: bool) -> Self {
        self.prove_unsat = prove_unsat;
        self
    }

    /// Enables CNF inprocessing (subsumption + bounded variable elimination)
    /// on the bit-blasting BV backend's Tseitin formula before SAT solving.
    #[must_use]
    pub fn with_cnf_inprocessing(mut self, cnf_inprocessing: bool) -> Self {
        self.cnf_inprocessing = cnf_inprocessing;
        self
    }

    /// Enables clause vivification within CNF inprocessing (between subsumption
    /// and `BVE`). A no-op unless [`Self::with_cnf_inprocessing`] is also on.
    /// See [`SolverConfig::cnf_vivify`].
    #[must_use]
    pub fn with_cnf_vivify(mut self, cnf_vivify: bool) -> Self {
        self.cnf_vivify = cnf_vivify;
        self
    }

    /// Enables denotation-preserving word-level preprocessing (canonicalization)
    /// before dispatch (Track 1, P1.2). See [`SolverConfig::preprocess`].
    #[must_use]
    pub fn with_preprocess(mut self, preprocess: bool) -> Self {
        self.preprocess = preprocess;
        self
    }

    /// Enables observational structural bit-demand profiling in the SAT-BV
    /// lowerer. See [`SolverConfig::profile_bit_demand`].
    #[must_use]
    pub fn with_bit_demand_profile(mut self, profile: bool) -> Self {
        self.profile_bit_demand = profile;
        self
    }

    /// Enables detailed cold CNF construction attribution.
    /// See [`SolverConfig::profile_cnf_construction`].
    #[must_use]
    pub fn with_cnf_construction_profile(mut self, profile: bool) -> Self {
        self.profile_cnf_construction = profile;
        self
    }

    /// Selects one cold bit-lowering strategy directly.
    #[must_use]
    pub fn with_bit_lowering_mode(mut self, mode: BitLoweringMode) -> Self {
        self.bit_lowering_mode = mode;
        self
    }

    /// Enables or disables demand-driven cold-path bit lowering (GQ4,
    /// ADR-0157).
    ///
    /// `true` selects [`BitLoweringMode::DemandSliced`]; `false` selects eager
    /// lowering. When chained with another mode selector, the last call wins.
    #[must_use]
    pub fn with_demand_bit_slicing(mut self, enabled: bool) -> Self {
        self.bit_lowering_mode = if enabled {
            BitLoweringMode::DemandSliced
        } else {
            BitLoweringMode::Eager
        };
        self
    }

    /// Enables admission-controlled range-demand lowering (GQ4-v2, ADR-0158).
    ///
    /// This selects [`BitLoweringMode::RangeSliced`]. When chained with another
    /// mode selector, the last call wins.
    #[must_use]
    pub fn with_range_demand_slicing(mut self, policy: RangeDemandPolicy) -> Self {
        self.bit_lowering_mode = BitLoweringMode::RangeSliced(policy);
        self
    }

    /// Whether dense demand-sliced lowering is selected.
    #[must_use]
    pub fn demand_bit_slicing(&self) -> bool {
        self.bit_lowering_mode == BitLoweringMode::DemandSliced
    }

    /// The selected range-demand policy, if any.
    #[must_use]
    pub fn range_demand_slicing(&self) -> Option<RangeDemandPolicy> {
        match self.bit_lowering_mode {
            BitLoweringMode::RangeSliced(policy) => Some(policy),
            BitLoweringMode::Eager | BitLoweringMode::DemandSliced => None,
        }
    }

    /// Enables bounded positive internal AND-tree half flattening in the warm
    /// incremental CNF encoder.
    #[must_use]
    pub fn with_incremental_positive_and_flattening(mut self, enabled: bool) -> Self {
        self.incremental_positive_and_flattening = enabled;
        self
    }

    /// Enables the CDCL(XOR) search fallback on `unknown` batsat results over
    /// XOR-structured formulas (ADR-0035). See [`SolverConfig::xor_cdcl_fallback`].
    #[must_use]
    pub fn with_xor_cdcl_fallback(mut self, xor_cdcl_fallback: bool) -> Self {
        self.xor_cdcl_fallback = xor_cdcl_fallback;
        self
    }

    /// Enables the lazy abstraction-refinement bit-blasting strategy (P2.1).
    /// See [`SolverConfig::lazy_bv`].
    #[must_use]
    pub fn with_lazy_bv(mut self, lazy_bv: bool) -> Self {
        self.lazy_bv = lazy_bv;
        self
    }

    /// Extends lazy bit-blasting to also abstract `ite`.
    /// See [`SolverConfig::lazy_bv_abstract_ite`].
    #[must_use]
    pub fn with_lazy_bv_abstract_ite(mut self, abstract_ite: bool) -> Self {
        self.lazy_bv_abstract_ite = abstract_ite;
        self
    }

    /// **Deprecated no-op (ADR-1703).** The native CDCL core is the primary SAT
    /// search unconditionally. See [`SolverConfig::native_cdcl`].
    #[must_use]
    pub fn with_native_cdcl(mut self, native_cdcl: bool) -> Self {
        self.native_cdcl = native_cdcl;
        self
    }

    /// Installs a progress sink for the proof-producing DRAT search. See
    /// [`SolverConfig::proof_progress`].
    #[must_use]
    pub fn with_proof_progress(mut self, proof_progress: ProofProgress) -> Self {
        self.proof_progress = Some(proof_progress);
        self
    }

    /// Installs a progress/bound sink for the checking stage that follows the
    /// proof-producing search on a `QF_BV` `unsat`. See
    /// [`SolverConfig::check_progress`].
    #[must_use]
    pub fn with_check_progress(mut self, check_progress: CheckProgress) -> Self {
        self.check_progress = Some(check_progress);
        self
    }
}

/// Layer-attributed measurements from the most recent check.
#[derive(Debug, Clone, Default, PartialEq)]
#[non_exhaustive]
pub struct SolveStats {
    /// Time spent translating Axeyum terms to the backend representation.
    pub translate: Duration,
    /// Time spent inside the backend's check.
    pub solve: Duration,
    /// Time spent lifting a satisfying backend model into Axeyum-owned values.
    pub model_lift: Duration,
    /// Unique DAG nodes translated.
    pub terms_translated: u64,
    /// Number of top-level assertions.
    pub assertion_count: u64,
    /// Backend-reported counters (name, value), e.g. Z3 statistics;
    /// contents are backend-specific and for post-mortems, not contracts.
    pub backend: Vec<(String, f64)>,
}

/// What a backend can do; not uniform across backends (backend-model note).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Capabilities {
    /// Human-readable backend name and version.
    pub name: String,
    /// Whether `Sat` results carry models.
    pub produces_models: bool,
    /// Whether the backend is refutation-complete for the M0 fragment
    /// (model-finding-only engines report `false`).
    pub complete: bool,
}

/// A solver backend: checks satisfiability of a conjunction of Boolean
/// terms from a [`TermArena`].
///
/// Backends deal only in Axeyum IDs and owned values; backend-internal
/// representations must not leak (api-design note). One-shot in M0;
/// incrementality extends this trait later rather than forking it.
pub trait SolverBackend {
    /// Reports what this backend supports.
    fn capabilities(&self) -> Capabilities;

    /// Checks the conjunction of `assertions` under `config`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::NonBooleanAssertion`] if any assertion is not
    /// `Bool`-sorted, [`SolverError::Unsupported`] for constructs the
    /// backend cannot express, or [`SolverError::Backend`] for internal
    /// backend failures. An undecided query is `Ok(CheckResult::Unknown)`.
    fn check(
        &mut self,
        arena: &TermArena,
        assertions: &[TermId],
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError>;

    /// Checks a first-class [`Query`].
    ///
    /// One-shot backends enforce active assumptions as ordinary assertions for
    /// now. Incremental backends can override this method later to use native
    /// assumption literals while preserving the same query semantics.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`SolverBackend::check`].
    fn check_query(
        &mut self,
        arena: &TermArena,
        query: &Query,
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        let assertions = query.solver_terms().collect::<Vec<_>>();
        self.check(arena, &assertions, config)
    }

    /// Layer-attributed measurements from the most recent `check`, if the
    /// backend records them. Telemetry is returned data, not logs
    /// (observability note).
    fn last_stats(&self) -> Option<&SolveStats> {
        None
    }
}
