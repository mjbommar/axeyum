//! Word-level preprocessing before solving (Track 1, P1.2).
//!
//! [`check_with_preprocessing`] shrinks a conjunction *before* it reaches a
//! backend by running the model-sound term-level passes — `propagate_values`
//! (pin `x = c`) then `solve_eqs` (substitute `x = t`) — composing their
//! [`ModelReconstructionTrail`]s. The backend then solves the smaller,
//! variable-reduced problem; on `sat` the trail reconstructs the eliminated
//! variables and the result is replayed against the **original** assertions, so
//! the returned [`Model`] is over the original query.
//!
//! This must run where the arena is mutable (the passes build substituted terms),
//! so it wraps the backend at the façade layer rather than living inside a
//! [`SolverBackend`], whose `check` takes an immutable arena. It mirrors
//! [`crate::check_with_array_elimination`].

use axeyum_ir::{TermArena, TermId, Value, eval};
use axeyum_rewrite::{propagate_values, solve_eqs};

use crate::backend::{CheckResult, SolverBackend, SolverConfig, SolverError};
use crate::model::Model;

/// Checks `assertions` with `backend` after model-sound word-level preprocessing.
///
/// # Errors
///
/// Returns [`SolverError`] from the backend, or [`SolverError::Backend`] if model
/// reconstruction or the original-assertion replay fails (a soundness alarm).
pub fn check_with_preprocessing<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Run the model-sound passes, composing their reconstruction trails in pass
    // order (propagate_values first, then solve_eqs).
    let (after_values, mut trail) = propagate_values(arena, assertions)
        .map_err(|error| SolverError::Backend(format!("propagate_values failed: {error}")))?
        .into_parts();
    let (reduced, eq_trail) = solve_eqs(arena, &after_values)
        .map_err(|error| SolverError::Backend(format!("solve_eqs failed: {error}")))?
        .into_parts();
    trail.append(eq_trail);

    let result = backend.check(arena, &reduced, config)?;
    let CheckResult::Sat(model) = result else {
        return Ok(result);
    };

    // Reconstruct the eliminated variables, then replay against the ORIGINAL
    // assertions — the same checkable-`sat` discipline as the array path.
    let reconstructed = trail
        .reconstruct(arena, &model.to_assignment())
        .map_err(|error| {
            SolverError::Backend(format!(
                "preprocessing model reconstruction failed: {error}"
            ))
        })?;

    for &assertion in assertions {
        match eval(arena, assertion, &reconstructed) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Err(SolverError::Backend(format!(
                    "preprocessed sat model replay failed: assertion #{} evaluated to false",
                    assertion.index()
                )));
            }
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "preprocessed sat model replay failed: assertion #{} evaluated to non-Boolean {value}",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "preprocessed sat model replay failed: assertion #{} failed evaluation: {error}",
                    assertion.index()
                )));
            }
        }
    }

    let mut out = Model::new();
    for (symbol, _name, _sort) in arena.symbols() {
        if let Some(value) = reconstructed.get(symbol) {
            out.set(symbol, value);
        }
    }
    Ok(CheckResult::Sat(out))
}
