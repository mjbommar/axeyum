//! Differential faithfulness checking of the `QF_BV` bit-blasting reduction
//! (track a — scalable assurance for the term→AIG step).
//!
//! Model replay certifies `sat` at the term level. For `unsat` there is no model
//! to replay, so the soundness of the *reduction* (a wrong bit-blasting could
//! turn a satisfiable term into an unsatisfiable CNF) is otherwise trusted. This
//! module adds a **scalable** assurance layer: it samples random assignments and
//! confirms the bit-blasted AIG evaluates to the **same value** as the original
//! term under the `axeyum-ir` evaluator. A disagreement is a *definitive*
//! bit-blasting faithfulness bug (a sound bug-detector, with a concrete
//! counterexample); agreement across many independent samples is real evidence
//! that the reduction did not distort the term — exactly where the term is too
//! large for the exhaustive [`crate::certify_qf_bv_by_enumeration`] certificate.
//!
//! It is sampling, not a proof: it cannot *certify* `unsat` end to end (that is
//! the open verified-bit-blaster program). It is the differential complement to
//! model replay, applied to the reduction itself, and it is deterministic (a
//! fixed seed) so a checker can reproduce it exactly.

use std::collections::BTreeMap;

use axeyum_bv::{first_unsupported_op, first_unsupported_sort, lower_terms};
use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, eval};

use crate::backend::SolverError;

/// The result of [`check_qf_bv_faithfulness`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FaithfulnessOutcome {
    /// The bit-blasted AIG agreed with the term evaluator on every sampled
    /// assignment (the count checked).
    Agreed {
        /// Number of random assignments evaluated on both sides.
        samples: u64,
    },
    /// A counterexample assignment was found where the AIG value and the term
    /// value disagree — a definitive faithfulness bug in the bit-blasting of the
    /// indicated root.
    Diverged {
        /// Index (into `roots`) of the term whose AIG value mismatched.
        root_index: usize,
    },
    /// The query uses an operator or sort the bit-blaster does not lower, so the
    /// reduction does not apply.
    Unsupported,
}

/// Differentially checks that the `QF_BV` bit-blasting of `roots` is faithful, by
/// evaluating the lowered AIG and the original terms on `samples` random
/// assignments drawn from a deterministic generator seeded by `seed`.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] if AIG evaluation or term evaluation fails
/// internally (an invariant violation, not a faithfulness counterexample — those
/// are reported as [`FaithfulnessOutcome::Diverged`]).
pub fn check_qf_bv_faithfulness(
    arena: &TermArena,
    roots: &[TermId],
    samples: u64,
    seed: u64,
) -> Result<FaithfulnessOutcome, SolverError> {
    // Reject anything the bit-blaster does not lower *before* lowering (it
    // `unreachable!`s on, e.g., integer terms rather than returning an error).
    if first_unsupported_sort(arena, roots).is_some()
        || first_unsupported_op(arena, roots).is_some()
    {
        return Ok(FaithfulnessOutcome::Unsupported);
    }
    let Ok(lowering) = lower_terms(arena, roots) else {
        return Ok(FaithfulnessOutcome::Unsupported);
    };

    // Distinct symbols and their sorts, from the lowering's symbol-bit inputs.
    let mut symbols: BTreeMap<axeyum_ir::SymbolId, Sort> = BTreeMap::new();
    for input in lowering.symbol_inputs() {
        symbols.insert(input.symbol, input.sort);
    }

    // A small linear-congruential generator keeps the sampling deterministic
    // (so the check is exactly reproducible — `seed` is part of the certificate).
    let mut state = seed | 1;
    let mut next = || {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        state
    };

    for _ in 0..samples {
        let mut assignment = Assignment::new();
        for (&symbol, &sort) in &symbols {
            assignment.set(symbol, random_value(sort, &mut next));
        }

        let aig_values = lowering
            .evaluate_roots(&assignment)
            .map_err(|error| SolverError::Backend(format!("faithfulness: AIG eval: {error}")))?;
        for (index, &root) in roots.iter().enumerate() {
            let term_value = eval(arena, root, &assignment).map_err(|error| {
                SolverError::Backend(format!("faithfulness: term eval: {error}"))
            })?;
            if aig_values.get(index) != Some(&term_value) {
                return Ok(FaithfulnessOutcome::Diverged { root_index: index });
            }
        }
    }

    Ok(FaithfulnessOutcome::Agreed { samples })
}

/// A random value of the given (finite, bit-blastable) sort.
fn random_value(sort: Sort, next: &mut impl FnMut() -> u64) -> Value {
    match sort {
        Sort::Bool => Value::Bool(next() & 1 == 1),
        Sort::BitVec(width) => {
            let bits = u128::from(next()) | (u128::from(next()) << 64);
            let mask = if width >= 128 {
                u128::MAX
            } else {
                (1u128 << width) - 1
            };
            Value::Bv {
                width,
                value: bits & mask,
            }
        }
        // `lower_terms` would have failed for any other sort, so this is
        // unreachable in practice; fall back to a Boolean to stay total.
        _ => Value::Bool(false),
    }
}
