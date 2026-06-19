//! Full theory composition: arrays + uninterpreted functions + bounded linear
//! integer arithmetic, all reduced to `QF_BV` (ADR-0010 + ADR-0013 + ADR-0014).
//!
//! [`check_with_all_theories`] is the most general entry point. It runs the
//! three eager reductions in dependency order —
//!
//! 1. **arrays** (`QF_AUFLIA` → `QF_UFLIA`): read-over-write + Ackermann;
//! 2. **functions** (`QF_UFLIA` → `QF_LIA`): Ackermann congruence;
//! 3. **integers** (`QF_LIA` → `QF_BV`): bounded signed bit-blasting —
//!
//! solves the pure-`QF_BV` result with any [`SolverBackend`], then projects the
//! model back in reverse (integer read-back → function interpretations → array
//! values) and replays it against the *original* assertions with the ground
//! evaluator. Each reduction is the same one used by the single-theory entry
//! points, so this subsumes them; a query using a subset of the theories simply
//! has the unused reductions act as the identity.
//!
//! **Soundness contract.** Array and function elimination are exact
//! (equisatisfiable), but integer bit-blasting is bounded. So when the query
//! contains integers, the result is reported conservatively: a bit-vector
//! `unsat` becomes `unknown` (a model may exist outside the width), and a
//! `sat` whose integer read-back fails to replay (width-`B` wraparound) becomes
//! `unknown`. Without integers, `unsat` is exact and a replay failure is a
//! soundness alarm.

use axeyum_ir::{TermArena, TermId, Value, eval};
use axeyum_rewrite::{
    ArrayElimError, FuncElimError, IntBlastError, blast_integers, eliminate_arrays,
    eliminate_functions,
};

use crate::backend::{
    CheckResult, SolverBackend, SolverConfig, SolverError, UnknownKind, UnknownReason,
};
use crate::model::Model;

/// Checks an arbitrary `QF_AUFLIA` conjunction with `backend`, composing array
/// elimination, function elimination, and bounded integer bit-blasting at
/// `int_width` bits.
///
/// The returned [`Model`] is over the original query (symbol values, array
/// values, function interpretations, and integer values). See the module docs
/// for the `sat`/`unsat`/`unknown` contract.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for constructs outside the supported
/// fragment (e.g. array equality), or [`SolverError`] from the backend. Bounded
/// incompleteness and out-of-range constants are [`CheckResult::Unknown`].
pub fn check_with_all_theories<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    int_width: u32,
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Reduction 1: arrays -> QF_UFLIA.
    let array_elim = eliminate_arrays(arena, assertions).map_err(map_array_error)?;
    let after_arrays = array_elim.assertions().to_vec();

    // Reduction 2: functions -> QF_LIA.
    let func_elim = eliminate_functions(arena, &after_arrays).map_err(map_func_error)?;
    let after_funcs = func_elim.assertions().to_vec();

    // Reduction 3: integers -> QF_BV.
    let int_blast = match blast_integers(arena, &after_funcs, int_width) {
        Ok(blasting) => blasting,
        Err(IntBlastError::ConstantOutOfRange { value, width }) => {
            return Ok(unknown(format!(
                "integer constant {value} does not fit the bounded width {width}; widen the bound"
            )));
        }
        Err(IntBlastError::InvalidWidth(width)) => {
            return Err(SolverError::Backend(format!(
                "invalid integer bit-blast width {width}"
            )));
        }
        Err(IntBlastError::Ir(error)) => return Err(SolverError::Backend(error.to_string())),
    };
    let has_integers = int_blast.had_integers();

    let result = backend.check(arena, int_blast.assertions(), config)?;
    let model = match result {
        CheckResult::Sat(model) => model,
        CheckResult::Unsat => {
            // Bounded integer search is incomplete for `unsat`; arrays and
            // functions are exact, so without integers the `unsat` stands.
            if has_integers {
                return Ok(unknown(format!(
                    "no model within the bounded integer width {}; widen the bound",
                    int_blast.width()
                )));
            }
            return Ok(CheckResult::Unsat);
        }
        CheckResult::Unknown(reason) => return Ok(CheckResult::Unknown(reason)),
    };

    // A `sat` model for an **arithmetic-sorted** uninterpreted function cannot yet be
    // projected: `project_model` keys function tables by scalar codes, which do not
    // exist for `Int`/`Real`. Degrade to a sound `Unknown` rather than panic (UNSAT
    // through this path is unaffected — it returns before model projection).
    if func_elim.had_functions() && has_arithmetic_function(arena) {
        return Ok(unknown(
            "sat model for an arithmetic-sorted uninterpreted function is unsupported \
             (combined path)"
                .to_owned(),
        ));
    }

    // Project the model back in reverse reduction order: integers (read-back),
    // then functions (their args are post-array, pre-integer scalars), then
    // arrays (a `select` index may mention a function application).
    let with_integers = int_blast.integer_model(&model.to_assignment());
    let with_functions = func_elim
        .project_model(arena, &with_integers)
        .map_err(|error| {
            SolverError::Backend(format!("function model projection failed: {error}"))
        })?;
    let projected = array_elim
        .project_model(arena, &with_functions)
        .map_err(|error| SolverError::Backend(format!("array model projection failed: {error}")))?;

    // Replay the projected model against the original assertions.
    for &assertion in assertions {
        match eval(arena, assertion, &projected) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                if has_integers {
                    return Ok(unknown(format!(
                        "bounded integer model overflowed at width {} (assertion #{} is false \
                         over exact semantics); widen the bound",
                        int_blast.width(),
                        assertion.index()
                    )));
                }
                return Err(SolverError::Backend(format!(
                    "combined sat model replay failed: assertion #{} evaluated to false",
                    assertion.index()
                )));
            }
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "combined sat model replay failed: assertion #{} evaluated to non-Boolean \
                     {value}",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "combined sat model replay failed: assertion #{} failed evaluation: {error}",
                    assertion.index()
                )));
            }
        }
    }

    // Build a model over the original query, dropping every internal fresh
    // variable and carrying symbol values, array values, and integer values.
    let mut out = Model::new();
    for (symbol, name, _sort) in arena.symbols() {
        if name.starts_with("!arr_sel_")
            || name.starts_with("!fn_app_")
            || name.starts_with("!int_bv_")
        {
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

/// Whether any declared uninterpreted function has an `Int`/`Real` parameter or
/// result — for such a function the `sat`-model projection (scalar-keyed function
/// tables) is not yet representable.
fn has_arithmetic_function(arena: &TermArena) -> bool {
    let is_arith = |s: &axeyum_ir::Sort| matches!(s, axeyum_ir::Sort::Int | axeyum_ir::Sort::Real);
    arena
        .functions()
        .any(|(_f, _n, params, result)| params.iter().any(is_arith) || is_arith(&result))
}

fn unknown(detail: String) -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail,
    })
}

fn map_array_error(error: ArrayElimError) -> SolverError {
    match error {
        ArrayElimError::Unsupported(what) => SolverError::Unsupported(what),
        ArrayElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    }
}

fn map_func_error(error: FuncElimError) -> SolverError {
    match error {
        FuncElimError::Unsupported(what) => SolverError::Unsupported(what),
        FuncElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    }
}
