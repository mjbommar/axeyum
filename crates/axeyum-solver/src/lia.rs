//! First-class bounded `QF_LIA` solving by bit-blasting to `QF_BV` (ADR-0014).
//!
//! [`check_with_int_blasting`] is the consumer-facing entry point for queries
//! over the integer sort: it bit-blasts integers to width-`B` signed
//! bit-vectors, solves the result with any [`SolverBackend`], and — crucially —
//! enforces the soundness contract by **reading the bit-vector model back as
//! exact integers and re-checking the original integer assertions** with the
//! ground evaluator.
//!
//! The bounded encoding is only an oracle for `sat`, and only after replay:
//!
//! - bit-vector `sat` + integer replay succeeds → genuine [`CheckResult::Sat`];
//! - bit-vector `sat` but integer replay fails (arithmetic wrapped at width `B`)
//!   → [`CheckResult::Unknown`] (the bound is too small for this model);
//! - bit-vector `unsat` → [`CheckResult::Unknown`] (no model *in range*; an
//!   unbounded model may exist) — never `unsat`;
//! - a constant that does not fit the bound → [`CheckResult::Unknown`].
//!
//! Pure `QF_BV` queries pass straight through unchanged.

use axeyum_ir::{TermArena, TermId, Value, eval};
use axeyum_rewrite::{IntBlastError, blast_integers};

use crate::backend::{
    CheckResult, SolverBackend, SolverConfig, SolverError, UnknownKind, UnknownReason,
};
use crate::model::Model;

/// The default bit-width used to bound integers when bit-blasting `QF_LIA`.
pub const DEFAULT_INT_WIDTH: u32 = 32;

/// Checks a (possibly integer-using) `QF_LIA` conjunction with `backend` by
/// bounded bit-blasting at `width` bits (use [`DEFAULT_INT_WIDTH`] for a
/// sensible default).
///
/// On a satisfiable bit-vector result the model is read back as exact integers
/// and the original integer assertions are replayed; the returned [`Model`] is
/// over the original query (integer symbols carry [`Value::Int`]). See the
/// module docs for the full `sat`/`unknown` contract.
///
/// # Errors
///
/// Returns [`SolverError`] from the backend. Bounded incompleteness and
/// out-of-range constants are [`CheckResult::Unknown`], never errors.
pub fn check_with_int_blasting<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    width: u32,
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let blasting = match blast_integers(arena, assertions, width) {
        Ok(blasting) => blasting,
        Err(IntBlastError::ConstantOutOfRange { value, width }) => {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: format!(
                    "integer constant {value} does not fit the bounded width {width}; \
                     widen the bound to decide this query"
                ),
            }));
        }
        Err(IntBlastError::InvalidWidth(width)) => {
            return Err(SolverError::Backend(format!(
                "invalid integer bit-blast width {width}"
            )));
        }
        Err(IntBlastError::UnsupportedOp(op)) => {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: format!(
                    "integer bit-blast does not support operator {op:?}; a specialized \
                     decider must handle this query"
                ),
            }));
        }
        Err(IntBlastError::Ir(error)) => {
            return Err(SolverError::Backend(error.to_string()));
        }
    };
    let eliminated = blasting.assertions().to_vec();
    let result = backend.check(arena, &eliminated, config)?;

    let CheckResult::Sat(model) = result else {
        // Bit-vector `unsat`/`unknown` only bounds the search; the integer
        // problem is undecided (a model may exist outside the range).
        if matches!(result, CheckResult::Unsat) && blasting.had_integers() {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: format!(
                    "no model within the bounded integer width {}; \
                     widen the bound to decide satisfiability",
                    blasting.width()
                ),
            }));
        }
        return Ok(result);
    };

    // Read the bit-vector model back as exact integers and re-check the original
    // integer assertions — the soundness anchor against width-`B` wraparound.
    let integer_model = blasting.integer_model(&model.to_assignment());
    for &assertion in assertions {
        match eval(arena, assertion, &integer_model) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Ok(CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::Incomplete,
                    detail: format!(
                        "bounded integer model overflowed at width {} (assertion #{} \
                         is false over exact integers); widen the bound",
                        blasting.width(),
                        assertion.index()
                    ),
                }));
            }
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "integer sat replay produced non-Boolean {value} for assertion #{}",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "integer sat replay failed for assertion #{}: {error}",
                    assertion.index()
                )));
            }
        }
    }

    // Build a model over the original query: drop the fresh bit-vector blast
    // variables, keep symbol values (integer symbols now carry `Value::Int`).
    let mut out = Model::new();
    for (symbol, name, _sort) in arena.symbols() {
        if name.starts_with("!int_bv_") {
            continue;
        }
        if let Some(value) = integer_model.get(symbol) {
            out.set(symbol, value);
        }
    }
    Ok(CheckResult::Sat(out))
}
