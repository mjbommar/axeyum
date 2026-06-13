//! First-class `QF_ABV` solving by eager array elimination (ADR-0010).
//!
//! [`check_with_array_elimination`] is the consumer-facing entry point for
//! queries that use `select`/`store`: it eagerly eliminates arrays to `QF_BV`,
//! solves the result with any [`SolverBackend`], and on `sat` projects the
//! model back to array values and replays it against the original array
//! assertions with the ground evaluator. Pure `QF_BV` queries pass straight
//! through unchanged.

use axeyum_ir::{TermArena, TermId, Value, eval};
use axeyum_rewrite::{ArrayElimError, eliminate_arrays};

use crate::backend::{CheckResult, SolverBackend, SolverConfig, SolverError};
use crate::model::Model;

/// Checks a (possibly array-using) `QF_ABV` conjunction with `backend`.
///
/// Arrays are eliminated to `QF_BV` by read-over-write + Ackermann reduction;
/// a `sat` model is projected back to array values and replayed against the
/// original assertions, so the returned [`Model`] is over the original query.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for array constructs outside the
/// supported fragment (e.g. array equality), or [`SolverError`] from the
/// backend. A `sat` model that fails to replay is a [`SolverError::Backend`].
pub fn check_with_array_elimination<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let elimination = eliminate_arrays(arena, assertions).map_err(map_elim_error)?;
    let eliminated = elimination.assertions().to_vec();
    let result = backend.check(arena, &eliminated, config)?;

    let CheckResult::Sat(model) = result else {
        return Ok(result);
    };

    let projected = elimination
        .project_model(arena, &model.to_assignment())
        .map_err(|error| SolverError::Backend(format!("array model projection failed: {error}")))?;

    for &assertion in assertions {
        match eval(arena, assertion, &projected) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Err(SolverError::Backend(format!(
                    "array sat model replay failed: assertion #{} evaluated to false",
                    assertion.index()
                )));
            }
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "array sat model replay failed: assertion #{} evaluated to non-Boolean {value}",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "array sat model replay failed: assertion #{} failed evaluation: {error}",
                    assertion.index()
                )));
            }
        }
    }

    // Build a model over the original query symbols (drop the internal fresh
    // select variables introduced by elimination).
    let mut out = Model::new();
    for (symbol, name, _sort) in arena.symbols() {
        if name.starts_with("!arr_sel_") {
            continue;
        }
        if let Some(value) = projected.get(symbol) {
            out.set(symbol, value);
        }
    }
    Ok(CheckResult::Sat(out))
}

fn map_elim_error(error: ArrayElimError) -> SolverError {
    match error {
        ArrayElimError::Unsupported(what) => SolverError::Unsupported(what),
        ArrayElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    }
}
