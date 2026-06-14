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

use axeyum_ir::{TermArena, TermId, Value, eval};

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
