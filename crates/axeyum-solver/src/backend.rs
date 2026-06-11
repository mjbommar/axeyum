//! The backend trait, results, configuration, and capabilities.

use std::time::Duration;

use axeyum_ir::{TermArena, TermId};

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
    /// The backend could not decide; the payload is a backend-specific
    /// reason (for example `"timeout"`).
    Unknown(String),
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
}

impl core::fmt::Display for SolverError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SolverError::NonBooleanAssertion(t) => {
                write!(f, "assertion #{} is not of Bool sort", t.index())
            }
            SolverError::Unsupported(what) => write!(f, "unsupported by backend: {what}"),
            SolverError::Backend(what) => write!(f, "backend failure: {what}"),
        }
    }
}

impl core::error::Error for SolverError {}

/// Per-query configuration.
///
/// M0 backends are one-shot, so the timeout is the cancellation mechanism;
/// a cooperative interrupt flag arrives with long-lived solver instances
/// (incrementality note).
#[derive(Debug, Clone, Default)]
pub struct SolverConfig {
    /// Wall-clock budget for the check; `None` means no limit.
    pub timeout: Option<Duration>,
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
}
