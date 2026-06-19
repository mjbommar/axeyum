//! First-class `QF_AUFBV` solving by composing the two eager-elimination
//! passes (ADR-0010 + ADR-0013).
//!
//! [`check_with_arrays_and_functions`] is the consumer-facing entry point for
//! queries that use **both** arrays (`select`/`store`) and uninterpreted
//! functions: it eliminates arrays to `QF_UFBV`, then eliminates functions to
//! `QF_BV`, solves with any [`SolverBackend`], and on `sat` projects the model
//! back through both passes (functions first, then arrays — array indices may
//! mention function applications) and replays it against the original
//! assertions with the ground evaluator. This is the theory-composition step:
//! two independent eager reductions, one shared bit-blasting core, one combined
//! checkable model.
//!
//! Pure `QF_BV` queries pass straight through; a query using only one theory
//! reduces to the corresponding single-theory path.

use axeyum_ir::{TermArena, TermId, Value, eval};
use axeyum_rewrite::{eliminate_arrays, eliminate_functions};

use crate::backend::{CheckResult, SolverBackend, SolverConfig, SolverError};
use crate::model::Model;

/// Checks a (possibly array- and function-using) `QF_AUFBV` conjunction with
/// `backend`.
///
/// Arrays are eliminated first (`QF_AUFBV` → `QF_UFBV`), then uninterpreted
/// functions (`QF_UFBV` → `QF_BV`). A `sat` model is projected back through
/// both passes and replayed against the original assertions, so the returned
/// [`Model`] is over the original query (carrying symbol values, array values,
/// and function interpretations).
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for constructs outside the supported
/// fragment (e.g. array equality), or [`SolverError`] from the backend. A `sat`
/// model that fails to replay is a [`SolverError::Backend`].
pub fn check_with_arrays_and_functions<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Pass 1: arrays -> QF_UFBV (function applications pass through untouched,
    // their arguments rewritten).
    let array_elim = eliminate_arrays(arena, assertions).map_err(|error| match error {
        axeyum_rewrite::ArrayElimError::Unsupported(what) => SolverError::Unsupported(what),
        axeyum_rewrite::ArrayElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    })?;
    let after_arrays = array_elim.assertions().to_vec();

    // Pass 2: functions -> QF_BV.
    let func_elim = eliminate_functions(arena, &after_arrays).map_err(|error| match error {
        axeyum_rewrite::FuncElimError::Unsupported(what) => SolverError::Unsupported(what),
        axeyum_rewrite::FuncElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    })?;
    let eliminated = func_elim.assertions().to_vec();

    let result = backend.check(arena, &eliminated, config)?;
    let CheckResult::Sat(model) = result else {
        return Ok(result);
    };

    // Defense-in-depth: an arithmetic-sorted (Int/Real) uninterpreted function has
    // no scalar-keyed sat-model projection, so degrade to a sound `Unknown` rather
    // than risk a `scalar_code` panic in `project_model`. (Reaching here with such a
    // function is unlikely — the bit-vector `backend` would not return `sat` on its
    // Int constraints — but the guard keeps the "never crash" invariant total.)
    if func_elim.had_functions() {
        let is_arith =
            |s: &axeyum_ir::Sort| matches!(s, axeyum_ir::Sort::Int | axeyum_ir::Sort::Real);
        if arena
            .functions()
            .any(|(_f, _n, params, result)| params.iter().any(is_arith) || is_arith(&result))
        {
            return Ok(CheckResult::Unknown(crate::backend::UnknownReason {
                kind: crate::backend::UnknownKind::Incomplete,
                detail: "sat model for an arithmetic-sorted uninterpreted function is \
                         unsupported (aufbv path)"
                    .to_owned(),
            }));
        }
    }

    // Project functions first: their eliminated argument terms are
    // post-array-elimination (no `select` remains), so they evaluate under the
    // base `QF_BV` model directly. Then project arrays: a `select` index may
    // mention a function application, so array projection needs the function
    // interpretations in scope.
    let with_functions = func_elim
        .project_model(arena, &model.to_assignment())
        .map_err(|error| {
            SolverError::Backend(format!("function model projection failed: {error}"))
        })?;
    let projected = array_elim
        .project_model(arena, &with_functions)
        .map_err(|error| SolverError::Backend(format!("array model projection failed: {error}")))?;

    for &assertion in assertions {
        match eval(arena, assertion, &projected) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Err(SolverError::Backend(format!(
                    "aufbv sat model replay failed: assertion #{} evaluated to false",
                    assertion.index()
                )));
            }
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "aufbv sat model replay failed: assertion #{} evaluated to non-Boolean {value}",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "aufbv sat model replay failed: assertion #{} failed evaluation: {error}",
                    assertion.index()
                )));
            }
        }
    }

    // Build a model over the original query: drop the internal fresh variables
    // from both passes, keep symbol values plus reconstructed array values and
    // function interpretations.
    let mut out = Model::new();
    for (symbol, name, _sort) in arena.symbols() {
        if name.starts_with("!arr_sel_") || name.starts_with("!fn_app_") {
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
