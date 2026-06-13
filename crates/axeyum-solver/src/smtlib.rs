//! The SMT-LIB text front door (ADR-0018).
//!
//! [`solve_smtlib`] is the entry point a real SMT consumer reaches for: it takes
//! a script as *text* — a file, an editor buffer, output from another tool —
//! parses it with [`axeyum_smtlib`], and decides it with [`crate::solve`]. The
//! whole path is text in, a checked `sat`/`unsat`/`unknown` out.
//!
//! The script's declared `(set-info :status ...)` is passed through unchanged in
//! [`SmtLibOutcome::expected_status`]; it is *not* consulted when solving, so a
//! caller can cross-check the decision against the benchmark's own ground truth.
//! The trust anchor stays exactly where it is in [`crate::solve`]: a `sat` model
//! is replayed against the original term through the ground evaluator.

use axeyum_smtlib::parse_script;

use crate::auto::solve;
use crate::backend::{CheckResult, SolverConfig, SolverError};

/// The result of deciding an SMT-LIB script, with the script's own declarations.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SmtLibOutcome {
    /// The decision for the conjunction of the script's assertions.
    pub result: CheckResult,
    /// The `set-logic` value, if the script declared one.
    pub logic: Option<String>,
    /// The declared `(set-info :status ...)` (`"sat"`/`"unsat"`/`"unknown"`), if
    /// present. Ground truth for cross-checking; never consulted when solving.
    pub expected_status: Option<String>,
}

/// Parses an SMT-LIB 2 script and decides it — the text front door.
///
/// The script's assertions are decided as a conjunction by [`crate::solve`],
/// which routes across every supported theory and quantifier mode and replays
/// any `sat` model against the original term. The returned
/// [`SmtLibOutcome::expected_status`] reflects the script's own declared
/// `:status` and is left for the caller to compare against
/// [`SmtLibOutcome::result`].
///
/// # Errors
///
/// - [`SolverError::Parse`] when the text is malformed or uses an SMT-LIB
///   construct outside the supported fragment.
/// - any [`SolverError`] from [`crate::solve`] (e.g. a non-Boolean assertion or
///   an internal backend failure).
pub fn solve_smtlib(input: &str, config: &SolverConfig) -> Result<SmtLibOutcome, SolverError> {
    let mut script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    let result = solve(&mut script.arena, &script.assertions, config)?;
    Ok(SmtLibOutcome {
        result,
        logic: script.logic,
        expected_status: script.status,
    })
}
