//! `MaxSAT` / weighted-`MaxSAT`: maximize the (weighted) number of satisfied soft
//! constraints subject to the hard ones.
//!
//! Z3/cvc5 expose this as optimization over soft assertions; it is the capstone
//! of the optimization work, composing cardinality summing
//! ([`crate::at_most`] family) with the bit-vector optimizer
//! ([`crate::maximize_bv`]). Each soft constraint contributes its (unit or given)
//! weight to a bit-vector sum when satisfied; maximizing that sum subject to the
//! hard constraints is `MaxSAT`. It reduces entirely to the sound, replayed
//! bit-vector theory — no new core machinery — and returns the optimal weight
//! ([`OptOutcome::Optimal`]), [`OptOutcome::Infeasible`] when the hard
//! constraints are unsatisfiable, or [`OptOutcome::Unknown`].

use axeyum_ir::{TermArena, TermId, Value, eval};

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownReason};
use crate::model::Model;
use crate::optimize::{OptOutcome, maximize_bv};

/// Maximizes how many of `soft` hold subject to all of `hard` (unweighted
/// `MaxSAT`). The optimum is the largest number of soft constraints simultaneously
/// satisfiable together with the hard constraints.
///
/// # Errors
///
/// Returns [`SolverError`] from the underlying optimizer / IR builders.
pub fn max_satisfiable(
    arena: &mut TermArena,
    hard: &[TermId],
    soft: &[TermId],
) -> Result<OptOutcome, SolverError> {
    let weighted: Vec<(TermId, u64)> = soft.iter().map(|&s| (s, 1)).collect();
    max_satisfiable_weighted(arena, hard, &weighted)
}

/// Weighted `MaxSAT`: maximizes the total weight of satisfied soft constraints
/// subject to all of `hard`. Each entry is `(soft constraint, weight)`.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if the total weight needs more than 127
/// bits, or [`SolverError`] from the optimizer / IR builders.
pub fn max_satisfiable_weighted(
    arena: &mut TermArena,
    hard: &[TermId],
    soft: &[(TermId, u64)],
) -> Result<OptOutcome, SolverError> {
    let total: u128 = soft.iter().map(|&(_, w)| u128::from(w)).sum();
    let width = weight_width(total)?;
    let zero = arena.bv_const(width, 0)?;
    let mut sum = zero;
    for &(constraint, weight) in soft {
        let value = arena.bv_const(width, u128::from(weight))?;
        let increment = arena.ite(constraint, value, zero)?;
        sum = arena.bv_add(sum, increment)?;
    }
    maximize_bv(arena, hard, sum)
}

/// A `MaxSAT` solution that carries the witnessing model, not just the optimum.
#[derive(Debug, Clone)]
pub enum MaxSatOutcome {
    /// The optimal total weight, a model achieving it, and which soft constraints
    /// that model satisfies (parallel to the input `soft`).
    Optimal {
        /// The optimal total satisfied weight.
        weight: i128,
        /// A model (over the original symbols) achieving the optimum; every `sat`
        /// is replay-checkable against the original assertions.
        model: Model,
        /// `satisfied[i]` is whether `soft[i]` holds in `model`.
        satisfied: Vec<bool>,
    },
    /// The hard constraints are unsatisfiable.
    Infeasible,
    /// A probe was undecided.
    Unknown(UnknownReason),
}

/// Like [`max_satisfiable`] but returns the **witnessing model** and the satisfied
/// soft-constraint set (z3's `MaxSAT` returns a model, not just the count).
///
/// # Errors
///
/// As [`max_satisfiable_weighted_model`].
pub fn max_satisfiable_model(
    arena: &mut TermArena,
    hard: &[TermId],
    soft: &[TermId],
) -> Result<MaxSatOutcome, SolverError> {
    let weighted: Vec<(TermId, u64)> = soft.iter().map(|&s| (s, 1)).collect();
    max_satisfiable_weighted_model(arena, hard, &weighted)
}

/// Weighted [`max_satisfiable_weighted`] that also returns the witnessing model and
/// the satisfied soft-constraint set. After finding the optimal weight `W`, it
/// pins the weight-sum to `W` and solves once more to extract a model, then
/// evaluates each soft constraint in it. Sound: the returned `sat` model is decided
/// by [`check_auto`] and re-evaluated here against the original soft constraints.
///
/// # Errors
///
/// [`SolverError::Unsupported`] if the total weight exceeds 127 bits, or
/// [`SolverError`] from the optimizer / solver / IR builders.
pub fn max_satisfiable_weighted_model(
    arena: &mut TermArena,
    hard: &[TermId],
    soft: &[(TermId, u64)],
) -> Result<MaxSatOutcome, SolverError> {
    let total: u128 = soft.iter().map(|&(_, w)| u128::from(w)).sum();
    let width = weight_width(total)?;
    let zero = arena.bv_const(width, 0)?;
    let mut sum = zero;
    for &(constraint, weight) in soft {
        let value = arena.bv_const(width, u128::from(weight))?;
        let increment = arena.ite(constraint, value, zero)?;
        sum = arena.bv_add(sum, increment)?;
    }
    let weight = match maximize_bv(arena, hard, sum)? {
        OptOutcome::Optimal(w) => w,
        OptOutcome::Infeasible => return Ok(MaxSatOutcome::Infeasible),
        // An unbounded weight is impossible (the sum is bounded by `total`); fold it
        // into `Unknown` defensively rather than panicking.
        OptOutcome::Unbounded => {
            return Ok(MaxSatOutcome::Unknown(UnknownReason {
                kind: crate::backend::UnknownKind::Incomplete,
                detail: "MaxSAT weight sum reported unbounded (unexpected)".to_owned(),
            }));
        }
        OptOutcome::Unknown(reason) => return Ok(MaxSatOutcome::Unknown(reason)),
    };

    // Pin the weight-sum at its optimum and solve once more to witness a model.
    #[allow(clippy::cast_sign_loss)]
    let w_const = arena.bv_const(width, weight as u128)?;
    let pin = arena.eq(sum, w_const)?;
    let mut query = hard.to_vec();
    query.push(pin);
    let model = match check_auto(arena, &query, &SolverConfig::default())? {
        CheckResult::Sat(model) => model,
        // The optimum was just shown achievable, so this is sat; treat a surprise
        // unsat/unknown as `Unknown` (never a wrong answer).
        CheckResult::Unsat | CheckResult::Unknown(_) => {
            return Ok(MaxSatOutcome::Unknown(UnknownReason {
                kind: crate::backend::UnknownKind::Incomplete,
                detail: "MaxSAT could not witness a model at the optimum".to_owned(),
            }));
        }
    };
    let assignment = model.to_assignment();
    let mut satisfied = Vec::with_capacity(soft.len());
    for &(constraint, _) in soft {
        satisfied.push(matches!(
            eval(arena, constraint, &assignment),
            Ok(Value::Bool(true))
        ));
    }
    Ok(MaxSatOutcome::Optimal {
        weight,
        model,
        satisfied,
    })
}

/// The minimal bit-width to hold the total weight (at least 1, at most 127 so the
/// bit-vector optimizer accepts it).
fn weight_width(total: u128) -> Result<u32, SolverError> {
    let bits = if total == 0 {
        1
    } else {
        u128::BITS - total.leading_zeros()
    };
    if bits > 127 {
        return Err(SolverError::Unsupported(format!(
            "MaxSAT total weight needs {bits} bits, over the 127-bit optimizer limit"
        )));
    }
    Ok(bits)
}
