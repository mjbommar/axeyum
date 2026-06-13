//! The backend trait, results, configuration, and capabilities.

use std::time::Duration;

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
    /// The assertions are satisfiable; the model maps every declared symbol
    /// to a value (backend model completion fills unconstrained symbols).
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

/// Errors from a backend invocation.
///
/// These are operational failures; an undecided query is
/// [`CheckResult::Unknown`], not an error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolverError {
    /// An assertion was not of Boolean sort.
    NonBooleanAssertion(TermId),
    /// The backend cannot represent part of the query.
    Unsupported(String),
    /// The backend failed internally (missing model, API failure).
    Backend(String),
    /// The input text could not be parsed (the SMT-LIB text front door).
    Parse(String),
}

impl core::fmt::Display for SolverError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SolverError::NonBooleanAssertion(t) => {
                write!(f, "assertion #{} is not of Bool sort", t.index())
            }
            SolverError::Unsupported(what) => write!(f, "unsupported by backend: {what}"),
            SolverError::Backend(what) => write!(f, "backend failure: {what}"),
            SolverError::Parse(what) => write!(f, "parse error: {what}"),
        }
    }
}

impl core::error::Error for SolverError {}

impl From<axeyum_ir::IrError> for SolverError {
    /// An IR builder error during solving is an internal backend failure.
    fn from(error: axeyum_ir::IrError) -> Self {
        SolverError::Backend(error.to_string())
    }
}

/// Per-query configuration.
///
/// Backends are one-shot for now, so budgets are the cancellation
/// mechanism; a cooperative interrupt flag arrives with long-lived solver
/// instances (incrementality note). Every budget exhaustion surfaces as
/// [`CheckResult::Unknown`] with a classified reason, never a hang.
#[derive(Debug, Clone, Default)]
pub struct SolverConfig {
    /// Wall-clock budget for the check; `None` means no limit.
    pub timeout: Option<Duration>,
    /// Deterministic resource budget (maps to Z3 `rlimit`); reproducible
    /// across machines, preferred for bisecting blowups.
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
    /// When set, an `unsat` result is independently re-derived by the
    /// proof-producing SAT core and its DRAT proof is verified before being
    /// returned (ADR-0011/0012). A disagreement or failed proof becomes a
    /// [`SolverError::Backend`] soundness alarm. The proof core is a reference,
    /// not scalable, so this is for small instances / high-assurance checks.
    pub prove_unsat: bool,
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

    /// Sets the deterministic resource budget (maps to Z3 `rlimit`).
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
