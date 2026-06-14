//! Linear integer optimization (a first slice of optimization modulo theories).
//!
//! Z3/cvc5 expose `maximize`/`minimize`; this provides the integer-linear case,
//! directly serving the "constrained program optimization" north star. It is
//! built **on top of** the sound conjunctive integer decision procedure
//! ([`crate::check_with_lia_simplex`], ADR-0020) by feasibility queries, so it
//! inherits that procedure's soundness with no new core machinery:
//!
//! - feasibility of `assertions` gives a starting objective value;
//! - an **exponential** search raises the bound `objective >= k` until it becomes
//!   unsatisfiable (or a magnitude cap suggests the objective is unbounded);
//! - a **binary** search then finds the largest `k` with `objective >= k`
//!   satisfiable — that `k` is the maximum.
//!
//! Every probe is a sound `unsat`/`sat` decision; the result is the exact optimum
//! when one exists, [`OptOutcome::Unbounded`] when the objective grows past the
//! magnitude cap, [`OptOutcome::Infeasible`] when the constraints are `unsat`, and
//! [`OptOutcome::Unknown`] if a probe is undecided. `minimize` is `maximize` of
//! the negated objective. Feasibility probes go through the Boolean-structured
//! integer oracle ([`crate::check_with_lia_dpll`]), so the constraints may be
//! arbitrary Boolean structure over integer atoms (disjunctions, implications),
//! not just conjunctions.

use axeyum_ir::{Sort, TermArena, TermId, Value, eval};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownReason};
use crate::dpll_lia::check_with_lia_dpll;

/// Doubling steps before the objective is declared unbounded. `2^126` overflows
/// `i128` magnitude, so this is effectively an overflow guard, not a real bound.
const MAX_DOUBLINGS: u32 = 126;

/// The result of a linear-integer optimization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OptOutcome {
    /// The exact optimal objective value.
    Optimal(i128),
    /// The objective is unbounded in the optimization direction.
    Unbounded,
    /// The constraints are unsatisfiable, so there is no optimum.
    Infeasible,
    /// A feasibility probe was undecided.
    Unknown(UnknownReason),
}

/// Maximizes the integer-linear `objective` subject to `assertions`.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if `objective` is not integer-sorted or
/// the query is outside the conjunctive integer fragment, or
/// [`SolverError::Backend`] on an internal error.
pub fn maximize_lia(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
) -> Result<OptOutcome, SolverError> {
    // Starting point: any feasible value of the objective.
    let mut lo = match objective_value(arena, assertions, objective)? {
        Probe::Sat(value) => value,
        Probe::Unsat => return Ok(OptOutcome::Infeasible),
        Probe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
    };

    // Exponential search for an unsatisfiable upper bound `hi` (objective >= hi
    // is infeasible). Bounded by MAX_DOUBLINGS / i128 overflow -> Unbounded.
    let mut delta: i128 = 1;
    let mut doublings: u32 = 0;
    let mut hi = loop {
        let Some(probe_point) = lo.checked_add(delta) else {
            return Ok(OptOutcome::Unbounded);
        };
        match objective_ge(arena, assertions, objective, probe_point)? {
            Probe::Sat(value) => lo = value.max(probe_point),
            Probe::Unsat => break probe_point,
            Probe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
        }
        doublings += 1;
        if doublings >= MAX_DOUBLINGS {
            return Ok(OptOutcome::Unbounded);
        }
        match delta.checked_mul(2) {
            Some(next) => delta = next,
            None => return Ok(OptOutcome::Unbounded),
        }
    };

    // Binary search in [lo, hi): objective >= lo is sat, objective >= hi is unsat.
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        match objective_ge(arena, assertions, objective, mid)? {
            Probe::Sat(value) => lo = value.max(mid),
            Probe::Unsat => hi = mid,
            Probe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
        }
    }
    Ok(OptOutcome::Optimal(lo))
}

/// Minimizes the integer-linear `objective` subject to `assertions`.
///
/// # Errors
///
/// See [`maximize_lia`].
pub fn minimize_lia(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
) -> Result<OptOutcome, SolverError> {
    let negated = arena.int_neg(objective)?;
    Ok(match maximize_lia(arena, assertions, negated)? {
        OptOutcome::Optimal(max_of_neg) => match max_of_neg.checked_neg() {
            Some(min) => OptOutcome::Optimal(min),
            None => OptOutcome::Unbounded,
        },
        other => other,
    })
}

/// The result of one feasibility probe.
enum Probe {
    /// Satisfiable, carrying the objective's value in the found model.
    Sat(i128),
    Unsat,
    Unknown(UnknownReason),
}

/// Decides `assertions` and, if satisfiable, returns the objective's value.
fn objective_value(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
) -> Result<Probe, SolverError> {
    decide_with_objective(arena, assertions, objective, None)
}

/// Decides `assertions AND objective >= bound` and returns the objective value.
fn objective_ge(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
    bound: i128,
) -> Result<Probe, SolverError> {
    decide_with_objective(arena, assertions, objective, Some(bound))
}

fn decide_with_objective(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
    bound: Option<i128>,
) -> Result<Probe, SolverError> {
    let mut query = assertions.to_vec();
    if let Some(bound) = bound {
        let bound_term = arena.int_const(bound);
        query.push(arena.int_ge(objective, bound_term)?);
    }
    // Use the Boolean-structured integer oracle so optimization works over
    // disjunctive/implicative constraints, not just conjunctions. (On a pure
    // conjunction it reduces to the same simplex decision.)
    match check_with_lia_dpll(arena, &query, &SolverConfig::default())? {
        CheckResult::Sat(model) => {
            let assignment = model.to_assignment();
            match eval(arena, objective, &assignment)? {
                Value::Int(value) => Ok(Probe::Sat(value)),
                other => Err(SolverError::Unsupported(format!(
                    "optimization objective is not integer-valued (got {other:?})"
                ))),
            }
        }
        CheckResult::Unsat => Ok(Probe::Unsat),
        CheckResult::Unknown(reason) => Ok(Probe::Unknown(reason)),
    }
}

// ---------------------------------------------------------------------------
// Unsigned bit-vector optimization.
//
// The bit-vector domain is finite, so there is no unbounded case and binary
// search on the objective bound terminates with the exact optimum. Probes go
// through the eager bit-vector solver (the full dispatcher), so the constraints
// may be arbitrary `QF_BV` (and the supported theory composition). Objectives
// wider than 127 bits are declined (the optimum may not fit the `i128` result).
// ---------------------------------------------------------------------------

/// Maximizes the **unsigned** value of bit-vector `objective` subject to
/// `assertions`.
///
/// # Errors
///
/// [`SolverError::Unsupported`] if `objective` is not a bit-vector of width
/// `<= 127`, or [`SolverError::Backend`] on an internal error.
pub fn maximize_bv(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
) -> Result<OptOutcome, SolverError> {
    let max = bv_objective_max(arena, objective)?;
    let v0 = match bv_value(arena, assertions, objective, None)? {
        BvProbe::Sat(value) => value,
        BvProbe::Unsat => return Ok(OptOutcome::Infeasible),
        BvProbe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
    };
    // Largest k in [v0, max] with `objective >=u k` satisfiable.
    let mut lo = v0;
    let mut hi = max;
    while lo < hi {
        let mid = lo + (hi - lo).div_ceil(2);
        match bv_value(arena, assertions, objective, Some((BvRel::Uge, mid)))? {
            BvProbe::Sat(value) => lo = value.max(mid),
            BvProbe::Unsat => hi = mid - 1,
            BvProbe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
        }
    }
    Ok(OptOutcome::Optimal(bv_to_i128(lo)?))
}

/// Minimizes the **unsigned** value of bit-vector `objective` subject to
/// `assertions`.
///
/// # Errors
///
/// See [`maximize_bv`].
pub fn minimize_bv(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
) -> Result<OptOutcome, SolverError> {
    bv_objective_max(arena, objective)?; // width check
    let v0 = match bv_value(arena, assertions, objective, None)? {
        BvProbe::Sat(value) => value,
        BvProbe::Unsat => return Ok(OptOutcome::Infeasible),
        BvProbe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
    };
    // Smallest k in [0, v0] with `objective <=u k` satisfiable.
    let mut lo = 0u128;
    let mut hi = v0;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        match bv_value(arena, assertions, objective, Some((BvRel::Ule, mid)))? {
            BvProbe::Sat(value) => hi = value.min(mid),
            BvProbe::Unsat => lo = mid + 1,
            BvProbe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
        }
    }
    Ok(OptOutcome::Optimal(bv_to_i128(lo)?))
}

/// Converts an unsigned optimum to `i128` (always succeeds for width <= 127,
/// which the callers enforce via [`bv_objective_max`]).
fn bv_to_i128(value: u128) -> Result<i128, SolverError> {
    i128::try_from(value).map_err(|_| {
        SolverError::Backend("bit-vector optimum exceeds the i128 result range".to_string())
    })
}

/// An unsigned bit-vector bound relation for an optimization probe.
#[derive(Clone, Copy)]
enum BvRel {
    Uge,
    Ule,
}

/// The maximum unsigned value of `objective`'s sort (and a width check).
fn bv_objective_max(arena: &TermArena, objective: TermId) -> Result<u128, SolverError> {
    match arena.sort_of(objective) {
        Sort::BitVec(width) if width <= 127 => {
            Ok(if width == 0 { 0 } else { (1u128 << width) - 1 })
        }
        Sort::BitVec(width) => Err(SolverError::Unsupported(format!(
            "bit-vector optimization objective width {width} exceeds 127"
        ))),
        other => Err(SolverError::Unsupported(format!(
            "bit-vector optimization objective is not a bit-vector (got {other:?})"
        ))),
    }
}

/// One bit-vector feasibility probe result, carrying the objective's unsigned
/// value in the found model.
enum BvProbe {
    Sat(u128),
    Unsat,
    Unknown(UnknownReason),
}

/// Decides `assertions` (optionally with an unsigned bound on `objective`) via
/// the eager bit-vector dispatcher and returns the objective's value.
fn bv_value(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
    bound: Option<(BvRel, u128)>,
) -> Result<BvProbe, SolverError> {
    let Sort::BitVec(width) = arena.sort_of(objective) else {
        unreachable!("bv_value called on a non-bit-vector objective")
    };
    let mut query = assertions.to_vec();
    if let Some((rel, value)) = bound {
        let bound_term = arena.bv_const(width, value)?;
        let constraint = match rel {
            BvRel::Uge => arena.bv_uge(objective, bound_term)?,
            BvRel::Ule => arena.bv_ule(objective, bound_term)?,
        };
        query.push(constraint);
    }
    match crate::auto::solve(arena, &query, &SolverConfig::default())? {
        CheckResult::Sat(model) => {
            let assignment = model.to_assignment();
            match eval(arena, objective, &assignment)? {
                Value::Bv { value, .. } => Ok(BvProbe::Sat(value)),
                other => Err(SolverError::Backend(format!(
                    "bv optimization objective evaluated to a non-bit-vector ({other:?})"
                ))),
            }
        }
        CheckResult::Unsat => Ok(BvProbe::Unsat),
        CheckResult::Unknown(reason) => Ok(BvProbe::Unknown(reason)),
    }
}
