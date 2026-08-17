//! [`SolverError`] — operational failures from a solve, as a leaf module.
//!
//! This type used to live in [`crate::backend`], which is where it is still
//! re-exported from, so the 60-odd `use crate::backend::SolverError` sites are
//! unchanged. It moved because `backend` is not a leaf: it pulls in
//! [`crate::model::Model`], and `model` in turn reaches the quantifier
//! certificate data. Anything that merely needs to *report* a failure was
//! therefore dragged into that graph, which is how
//!
//!     backend → model → quant_sat_certificates → proof → backend
//!
//! closed into a four-module cycle when `quant_sat_certificates` was split out
//! (25ab64649). `proof` was in it for one reason: it names `SolverError` in its
//! `Result` types. An error type is a leaf concept and should not be able to
//! create a cycle by being mentioned.
//!
//! `scripts/analyze_solver_module_graph.py --check` is the gate; see
//! `docs/refactor-2026-08/03-solver-decomposition.md`.

use axeyum_ir::TermId;

/// Errors from a backend invocation.
///
/// These are operational failures; an undecided query is
/// [`CheckResult::Unknown`](crate::CheckResult::Unknown), not an error.
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
