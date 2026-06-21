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

use crate::backend::{
    CheckResult, SolverBackend, SolverConfig, SolverError, UnknownKind, UnknownReason,
};
use crate::model::Model;

/// A sound `Unknown` with an `Incomplete` reason — the decline target for a
/// projection that cannot be reconstructed or a `sat` model that fails replay.
fn unknown(detail: String) -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail,
    })
}

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
/// model whose projection fails to reconstruct or fails to replay declines to a
/// sound [`CheckResult::Unknown`] — never an error (`unknown` is first-class).
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

    // Project functions first: their eliminated argument terms are
    // post-array-elimination (no `select` remains), so they evaluate under the
    // base `QF_BV` model directly. Then project arrays: a `select` index may
    // mention a function application, so array projection needs the function
    // interpretations in scope.
    //
    // An **arithmetic-sorted** (`Int`/`Real`) uninterpreted function now projects to
    // a full-`Value`-keyed interpretation (`project_model`, crash-safe), so the early
    // arith-UF bail is gone: we ATTEMPT the projection and let the replay check below
    // be the soundness anchor. A projection that cannot be reconstructed (e.g. a
    // nested arith-sorted application whose fresh symbol is unassigned in the base
    // model) returns `Err` → a sound `Unknown`, NOT a backend error ("`unknown` is
    // first-class, never an error"). A wrong projection can only make the replay fail
    // (→ decline), never accept a wrong `sat`.
    let with_functions = match func_elim.project_model(arena, &model.to_assignment()) {
        Ok(projected) => projected,
        Err(error) => {
            return Ok(unknown(format!(
                "function model projection failed (aufbv path): {error}"
            )));
        }
    };
    let projected = match array_elim.project_model(arena, &with_functions) {
        Ok(projected) => projected,
        Err(error) => {
            return Ok(unknown(format!(
                "array model projection failed (aufbv path): {error}"
            )));
        }
    };

    // REPLAY CHECK (the soundness anchor): every original assertion must evaluate to
    // `Bool(true)` under the projected model through the ground evaluator (which
    // consults the projected UF interpretation for `Op::Apply`). Array and function
    // elimination are exact, so any non-`true`/indeterminate replay is a sound decline
    // to `Unknown` — never an emitted (possibly wrong) `Sat`, matching euf's strictness.
    for &assertion in assertions {
        match eval(arena, assertion, &projected) {
            Ok(Value::Bool(true)) => {}
            Ok(_) | Err(_) => {
                return Ok(unknown(format!(
                    "aufbv sat model replay did not confirm assertion #{}",
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
