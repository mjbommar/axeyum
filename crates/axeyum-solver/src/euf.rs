//! First-class `QF_UFBV` solving by eager Ackermann elimination (ADR-0013).
//!
//! [`check_with_function_elimination`] is the consumer-facing entry point for
//! queries that use uninterpreted-function applications: it eagerly eliminates
//! functions to `QF_BV` by Ackermann congruence reduction, solves the result
//! with any [`SolverBackend`], and on `sat` projects the model back to function
//! interpretations and replays it against the original assertions with the
//! ground evaluator. Pure `QF_BV` queries pass straight through unchanged.

use axeyum_ir::{TermArena, TermId, Value, eval};
use axeyum_rewrite::{FuncElimError, eliminate_functions};

use crate::backend::{CheckResult, SolverBackend, SolverConfig, SolverError};
use crate::model::Model;

/// Checks a (possibly function-using) `QF_UFBV` conjunction with `backend`.
///
/// Uninterpreted functions are eliminated to `QF_BV` by Ackermann congruence
/// reduction; a `sat` model is projected back to function interpretations and
/// replayed against the original assertions, so the returned [`Model`] is over
/// the original query (carrying both symbol values and function
/// interpretations).
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for constructs outside the supported
/// fragment, or [`SolverError`] from the backend. A `sat` model that fails to
/// replay is a [`SolverError::Backend`].
pub fn check_with_function_elimination<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let elimination = eliminate_functions(arena, assertions).map_err(map_elim_error)?;
    let eliminated = elimination.assertions().to_vec();
    let result = backend.check(arena, &eliminated, config)?;

    let CheckResult::Sat(model) = result else {
        return Ok(result);
    };

    let projected = elimination
        .project_model(arena, &model.to_assignment())
        .map_err(|error| {
            SolverError::Backend(format!("function model projection failed: {error}"))
        })?;

    for &assertion in assertions {
        match eval(arena, assertion, &projected) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Err(SolverError::Backend(format!(
                    "function sat model replay failed: assertion #{} evaluated to false",
                    assertion.index()
                )));
            }
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "function sat model replay failed: assertion #{} evaluated to non-Boolean {value}",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "function sat model replay failed: assertion #{} failed evaluation: {error}",
                    assertion.index()
                )));
            }
        }
    }

    // Build a model over the original query (drop the internal fresh
    // application variables) carrying both symbol values and reconstructed
    // function interpretations.
    let mut out = Model::new();
    for (symbol, name, _sort) in arena.symbols() {
        if name.starts_with("!fn_app_") {
            continue;
        }
        if let Some(value) = projected.get(symbol) {
            out.set(symbol, value);
        }
    }
    for (func, _name, _params, _result) in arena.functions() {
        if let Some(interp) = projected.function(func) {
            out.set_function(func, interp.clone());
        }
    }
    Ok(CheckResult::Sat(out))
}

fn map_elim_error(error: FuncElimError) -> SolverError {
    match error {
        FuncElimError::Unsupported(what) => SolverError::Unsupported(what),
        FuncElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    }
}
