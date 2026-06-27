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
use crate::optimize::{
    OptOutcome, minimize_bv_signed_with_config, minimize_bv_with_config, minimize_lia_with_config,
};

/// One lexicographic objective for model minimization.
///
/// The plain [`Self::Symbol`] variant uses this minimizer's default order for
/// the symbol sort: `false < true` for Bool, unsigned order for bit-vectors,
/// and mathematical order for Int. [`Self::SignedBv`] uses two's-complement
/// signed order for a bit-vector symbol, subject to the signed BV optimizer's
/// supported width range.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ModelMinimizeObjective {
    /// Minimize this symbol in its default sort order.
    Symbol(SymbolId),
    /// Minimize this bit-vector symbol in signed two's-complement order.
    SignedBv(SymbolId),
}

impl ModelMinimizeObjective {
    /// Returns the symbol optimized by this objective.
    #[must_use]
    pub fn symbol(self) -> SymbolId {
        match self {
            Self::Symbol(symbol) | Self::SignedBv(symbol) => symbol,
        }
    }

    fn signed_bv(self) -> bool {
        matches!(self, Self::SignedBv(_))
    }
}

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
    let objectives: Vec<ModelMinimizeObjective> = symbols
        .iter()
        .copied()
        .map(ModelMinimizeObjective::Symbol)
        .collect();
    minimize_model_objectives_with_config(arena, assertions, &objectives, config)
}

/// Minimizes a satisfying model for `assertions` over richer objective metadata.
///
/// This is the same strict, replay-checked contract as [`minimize_model`], but
/// each objective can request signed two's-complement order for a bit-vector
/// symbol. Signed BV objectives use the signed BV optimizer, currently limited
/// to widths up to 64 bits.
///
/// # Errors
///
/// See [`minimize_model`].
pub fn minimize_model_objectives(
    arena: &mut TermArena,
    assertions: &[TermId],
    objectives: &[ModelMinimizeObjective],
) -> Result<ModelMinimizeOutcome, SolverError> {
    minimize_model_objectives_with_config(arena, assertions, objectives, &SolverConfig::default())
}

/// Like [`minimize_model_objectives`], honoring `config` for every probe.
///
/// # Errors
///
/// See [`minimize_model`].
pub fn minimize_model_objectives_with_config(
    arena: &mut TermArena,
    assertions: &[TermId],
    objectives: &[ModelMinimizeObjective],
    config: &SolverConfig,
) -> Result<ModelMinimizeOutcome, SolverError> {
    let mut constraints = assertions.to_vec();
    let mut seen = BTreeSet::new();

    match solve_probe(arena, &constraints, config)? {
        ModelMinimizeOutcome::Minimized(_) => {}
        other => return Ok(other),
    }

    for &objective in objectives {
        let symbol = objective.symbol();
        if !seen.insert(symbol) {
            continue;
        }
        let term = arena.var(symbol);
        let sort = arena.sort_of(term);
        if objective.signed_bv() && !matches!(sort, Sort::BitVec(_)) {
            return Err(SolverError::Unsupported(format!(
                "signed BV model minimization objective requires a bit-vector symbol (got {sort:?})"
            )));
        }
        let pin = match sort {
            Sort::Bool => minimize_bool_symbol(arena, &constraints, term, config)?,
            Sort::BitVec(width) => minimize_bv_symbol(
                arena,
                &constraints,
                term,
                width,
                objective.signed_bv(),
                config,
            )?,
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
    signed: bool,
    config: &SolverConfig,
) -> Result<PinOutcome, SolverError> {
    let outcome = if signed {
        minimize_bv_signed_with_config(arena, constraints, term, config)?
    } else {
        minimize_bv_with_config(arena, constraints, term, config)?
    };
    match outcome {
        OptOutcome::Optimal(value) => {
            let value = if signed {
                i128_to_bv_bits(width, value)
            } else {
                u128::try_from(value).map_err(|_| {
                    SolverError::Backend(
                        "unsigned BV minimization returned a negative value".to_owned(),
                    )
                })?
            };
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

fn i128_to_bv_bits(width: u32, value: i128) -> u128 {
    if width >= 128 {
        u128::from_le_bytes(value.to_le_bytes())
    } else {
        let mask = (1u128 << width) - 1;
        u128::from_le_bytes(value.to_le_bytes()) & mask
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
