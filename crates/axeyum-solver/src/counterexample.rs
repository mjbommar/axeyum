//! Counterexample/model minimization helpers.
//!
//! The consumer-facing use case is property checking: after proving
//! `hyps ∧ ¬goal` satisfiable, callers want the smallest failing input rather
//! than an arbitrary replay-checked model. This module provides a deterministic
//! lexicographic minimizer over selected scalar symbols, built from the existing
//! checked decision and optimization front doors.

use std::collections::BTreeSet;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::model::Model;
use crate::optimize::{OptOutcome, minimize_bv_with_config, minimize_lia_with_config};

/// Outcome of a model-minimization request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModelMinimizeOutcome {
    /// The assertions are satisfiable and `model` is lexicographically minimal
    /// over the requested symbols in their input order.
    Minimized(Model),
    /// The assertions are unsatisfiable, so no counterexample/model exists.
    Infeasible,
    /// A decision or optimization probe was undecided.
    Unknown(UnknownReason),
}

/// Minimizes a satisfying model for `assertions` over `symbols`.
///
/// Symbols are optimized lexicographically in the order provided by `symbols`.
/// Supported objective sorts are:
///
/// - `Bool`, preferring `false` before `true`;
/// - unsigned `BitVec(w)` where `w <= 127`;
/// - `Int`, using the mathematical integer order.
///
/// Every optimization probe goes through the configured solver routes, and the
/// returned model is produced by a final satisfiability check under the optimal
/// pins, so it is replay-checked against the original assertions and the pins.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if a requested symbol has an unsupported
/// sort for this minimizer, or propagates a genuine backend/build error.
pub fn minimize_model(
    arena: &mut TermArena,
    assertions: &[TermId],
    symbols: &[SymbolId],
) -> Result<ModelMinimizeOutcome, SolverError> {
    minimize_model_with_config(arena, assertions, symbols, &SolverConfig::default())
}

/// Like [`minimize_model`], honoring `config` for every solve/optimization
/// probe.
///
/// # Errors
///
/// See [`minimize_model`].
pub fn minimize_model_with_config(
    arena: &mut TermArena,
    assertions: &[TermId],
    symbols: &[SymbolId],
    config: &SolverConfig,
) -> Result<ModelMinimizeOutcome, SolverError> {
    let mut constraints = assertions.to_vec();
    let mut seen = BTreeSet::new();

    match solve_probe(arena, &constraints, config)? {
        ModelMinimizeOutcome::Minimized(_) => {}
        other => return Ok(other),
    }

    for &symbol in symbols {
        if !seen.insert(symbol) {
            continue;
        }
        let term = arena.var(symbol);
        let pin = match arena.sort_of(term) {
            Sort::Bool => minimize_bool_symbol(arena, &constraints, term, config)?,
            Sort::BitVec(width) => minimize_bv_symbol(arena, &constraints, term, width, config)?,
            Sort::Int => minimize_int_symbol(arena, &constraints, term, config)?,
            other => {
                return Err(SolverError::Unsupported(format!(
                    "model minimization does not support symbol sort {other:?}"
                )));
            }
        };
        match pin {
            PinOutcome::Pin(pin) => constraints.push(pin),
            PinOutcome::Infeasible => return Ok(ModelMinimizeOutcome::Infeasible),
            PinOutcome::Unknown(reason) => return Ok(ModelMinimizeOutcome::Unknown(reason)),
        }
    }

    solve_probe(arena, &constraints, config)
}

fn minimize_bool_symbol(
    arena: &mut TermArena,
    constraints: &[TermId],
    term: TermId,
    config: &SolverConfig,
) -> Result<PinOutcome, SolverError> {
    let false_pin = arena.not(term)?;
    let mut query = constraints.to_vec();
    query.push(false_pin);
    match solve_probe(arena, &query, config)? {
        ModelMinimizeOutcome::Minimized(_) => Ok(PinOutcome::Pin(false_pin)),
        ModelMinimizeOutcome::Infeasible => Ok(PinOutcome::Pin(term)),
        ModelMinimizeOutcome::Unknown(reason) => Ok(PinOutcome::Unknown(reason)),
    }
}

fn minimize_bv_symbol(
    arena: &mut TermArena,
    constraints: &[TermId],
    term: TermId,
    width: u32,
    config: &SolverConfig,
) -> Result<PinOutcome, SolverError> {
    match minimize_bv_with_config(arena, constraints, term, config)? {
        OptOutcome::Optimal(value) => {
            let value = u128::try_from(value).map_err(|_| {
                SolverError::Backend(
                    "unsigned BV minimization returned a negative value".to_owned(),
                )
            })?;
            let constant = arena.bv_const(width, value)?;
            Ok(PinOutcome::Pin(arena.eq(term, constant)?))
        }
        OptOutcome::Infeasible => Ok(PinOutcome::Infeasible),
        OptOutcome::Unbounded => Err(SolverError::Backend(
            "BV minimization unexpectedly reported an unbounded objective".to_owned(),
        )),
        OptOutcome::Unknown(reason) => Ok(PinOutcome::Unknown(reason)),
    }
}

fn minimize_int_symbol(
    arena: &mut TermArena,
    constraints: &[TermId],
    term: TermId,
    config: &SolverConfig,
) -> Result<PinOutcome, SolverError> {
    match minimize_lia_with_config(arena, constraints, term, config)? {
        OptOutcome::Optimal(value) => {
            let constant = arena.int_const(value);
            Ok(PinOutcome::Pin(arena.eq(term, constant)?))
        }
        OptOutcome::Infeasible => Ok(PinOutcome::Infeasible),
        OptOutcome::Unbounded => Ok(PinOutcome::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: "integer model minimization is unbounded below".to_owned(),
        })),
        OptOutcome::Unknown(reason) => Ok(PinOutcome::Unknown(reason)),
    }
}

enum PinOutcome {
    Pin(TermId),
    Infeasible,
    Unknown(UnknownReason),
}

fn solve_probe(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<ModelMinimizeOutcome, SolverError> {
    match crate::check_auto(arena, assertions, config)? {
        CheckResult::Sat(model) => Ok(ModelMinimizeOutcome::Minimized(model)),
        CheckResult::Unsat => Ok(ModelMinimizeOutcome::Infeasible),
        CheckResult::Unknown(reason) => Ok(ModelMinimizeOutcome::Unknown(reason)),
    }
}
