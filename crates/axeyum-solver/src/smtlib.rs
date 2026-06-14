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

use axeyum_ir::Sort;
use axeyum_smtlib::{ScriptCommand, parse_script};

use crate::auto::{solve, unsat_core};
use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::optimize::{
    OptOutcome, maximize_bv, maximize_lia, minimize_bv, minimize_lia,
};

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

/// Solves an **optimization** (OMT) SMT-LIB script: each `(maximize t)` /
/// `(minimize t)` objective is optimized subject to the script's assertions,
/// returning one [`OptOutcome`] per objective in script order (the boxed /
/// independent interpretation). The objective sort selects the engine — `Int`
/// uses the simplex-bounded integer optimizer, `BitVec` the unsigned bit-vector
/// optimizer — and each `Optimal` value is anchored by the underlying optimizer's
/// model checks (ADR-0020 / the optimize module).
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text, [`SolverError::Unsupported`]
/// for an objective outside the supported (`Int`/`BitVec`) optimization
/// fragment, or any [`SolverError`] from the optimizer.
pub fn optimize_smtlib(input: &str, config: &SolverConfig) -> Result<Vec<OptOutcome>, SolverError> {
    let _ = config;
    let mut script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    let objectives = std::mem::take(&mut script.objectives);
    let mut outcomes = Vec::with_capacity(objectives.len());
    for (objective, is_max) in objectives {
        let outcome = match (script.arena.sort_of(objective), is_max) {
            (Sort::Int, true) => maximize_lia(&mut script.arena, &script.assertions, objective)?,
            (Sort::Int, false) => minimize_lia(&mut script.arena, &script.assertions, objective)?,
            (Sort::BitVec(_), true) => {
                maximize_bv(&mut script.arena, &script.assertions, objective)?
            }
            (Sort::BitVec(_), false) => {
                minimize_bv(&mut script.arena, &script.assertions, objective)?
            }
            (other, _) => {
                return Err(SolverError::Unsupported(format!(
                    "optimization objective of sort {other:?} (only Int and BitVec are supported)"
                )));
            }
        };
        outcomes.push(outcome);
    }
    Ok(outcomes)
}

/// Evaluates the `(get-value (t …))` terms of an SMT-LIB script against a `sat`
/// model. The conjunction of all assertions is decided; on `sat` each requested
/// term is evaluated through the ground evaluator under the model, returning the
/// values in script order. Returns `Ok(None)` when the script is `unsat`/
/// `unknown` (no model) or requested no values.
///
/// This is the model-query companion to [`solve_smtlib`]: the same trusted `sat`
/// model that is replay-checked is what the values are read from.
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text, any [`SolverError`]
/// from [`crate::solve`], or [`SolverError::Backend`] if a requested term fails
/// to evaluate under the model.
pub fn solve_smtlib_get_value(
    input: &str,
    config: &SolverConfig,
) -> Result<Option<Vec<axeyum_ir::Value>>, SolverError> {
    let mut script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    if script.get_value_terms.is_empty() {
        return Ok(None);
    }
    let CheckResult::Sat(model) = solve(&mut script.arena, &script.assertions, config)? else {
        return Ok(None);
    };
    let assignment = model.to_assignment();
    let mut values = Vec::with_capacity(script.get_value_terms.len());
    for &term in &script.get_value_terms {
        let value = axeyum_ir::eval(&script.arena, term, &assignment)
            .map_err(|e| SolverError::Backend(format!("get-value evaluation failed: {e}")))?;
        values.push(value);
    }
    Ok(Some(values))
}

/// Extracts an **unsat core** from an SMT-LIB script (`get-unsat-core`): the
/// conjunction of all its assertions is decided, and if it is `unsat`, a minimal
/// unsatisfiable subset is returned, reported as the assertions' `:named` labels
/// where present (and `assertion #i` otherwise, in script order). Returns
/// `Ok(None)` when the script is `sat`/`unknown` (no core exists).
///
/// The core is the deletion-minimized subset from [`crate::unsat_core`], so every
/// returned name is genuinely needed for unsatisfiability.
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text, or any [`SolverError`]
/// from the underlying [`crate::unsat_core`] solving.
pub fn solve_smtlib_unsat_core(
    input: &str,
    config: &SolverConfig,
) -> Result<Option<Vec<String>>, SolverError> {
    let mut script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    let Some(core) = unsat_core(&mut script.arena, &script.assertions, config)? else {
        return Ok(None);
    };
    let names = core
        .into_iter()
        .map(|i| {
            script
                .assertion_names
                .get(i)
                .and_then(Clone::clone)
                .unwrap_or_else(|| format!("assertion #{i}"))
        })
        .collect();
    Ok(Some(names))
}

/// Decides an **incremental** SMT-LIB script, returning one result per
/// `check-sat` in order (ADR-0009 lifecycle, ADR-0018 front door).
///
/// `push`/`pop` scope the assertion stack: `(push n)` opens `n` nested scopes,
/// `(pop n)` drops the assertions made within the `n` innermost ones, and each
/// `check-sat` decides the conjunction of the currently-active assertions.
/// `(check-sat-assuming (l …))` decides the active assertions together with the
/// assumption literals `l`, *without* retaining them past that query. The
/// decision at each `check-sat` is by [`crate::solve`] over that assertion set —
/// re-solved from scratch, which is *semantically equivalent* to incremental
/// solving (the warm-restart backends, ADR-0009, are a performance path, not a
/// soundness one). Declarations are global (the shared arena keeps them), which
/// is sound for deciding the assertion sets even across `pop`.
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text, or any
/// [`SolverError`] from a per-`check-sat` [`crate::solve`].
pub fn solve_smtlib_incremental(
    input: &str,
    config: &SolverConfig,
) -> Result<Vec<CheckResult>, SolverError> {
    let mut script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    let mut stack: Vec<axeyum_ir::TermId> = Vec::new();
    let mut scopes: Vec<usize> = Vec::new(); // assertion-stack depth at each open push
    let mut results = Vec::new();
    for command in &script.commands {
        match command {
            ScriptCommand::Assert(t) => stack.push(*t),
            ScriptCommand::Push(n) => {
                for _ in 0..*n {
                    scopes.push(stack.len());
                }
            }
            ScriptCommand::Pop(n) => {
                for _ in 0..*n {
                    if let Some(depth) = scopes.pop() {
                        stack.truncate(depth);
                    }
                }
            }
            ScriptCommand::CheckSat => {
                results.push(solve(&mut script.arena, &stack, config)?);
            }
            ScriptCommand::CheckSatAssuming(assumptions) => {
                // Decide the active assertions together with the assumptions, but
                // do not retain them: solve a temporary stack, then discard.
                let mut with = stack.clone();
                with.extend_from_slice(assumptions);
                results.push(solve(&mut script.arena, &with, config)?);
            }
        }
    }
    Ok(results)
}
