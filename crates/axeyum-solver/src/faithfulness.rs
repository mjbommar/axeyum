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
//!
//! # No in-crate caller by design (ADR-1812)
//!
//! This is an **assurance instrument, not a step of a decision**. Calling it on
//! every solve would slow the front door to buy evidence nobody reads; it is
//! meant to be pointed at a term deliberately, by a test, a fuzz harness, or a
//! checker. Its exhaustive sibling
//! [`crate::bitblast_miter`] — which replaced the sampling with
//! a DRAT-checked miter against an independently coded reference bit-blaster —
//! is what the gates use, and it has no in-crate caller either, for the same
//! reason (it is reached from `axeyum-bench` and `axeyum-verify`).
//!
//! The two are not redundant: the miter's refutation is a SAT call that grows
//! with the term, while this is `O(samples)` and stays cheap exactly where the
//! miter stops being affordable. Deleting it would lose the cheap end of that
//! trade, so it stays.

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

    let mut next = sample_stream(seed);

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

/// The deterministic sample stream behind `seed`: a linear-congruential
/// generator (so the check is exactly reproducible — `seed` is part of the
/// certificate) whose OUTPUT is passed through SplitMix64's finalizer.
///
/// The raw state is never handed out. Bit `k` of an LCG modulo `2^64` has
/// period `2^(k+1)`, so bit 0 alternates on every draw and, with two draws per
/// bit-vector symbol, every symbol's low bit landed on the same parity on every
/// sample: measured 2026-09-16 (lane ax-proptest), across 1000 samples of two
/// 6-bit symbols the divisor was never zero, no operand was ever odd, and only
/// 16 of the 64 values were ever drawn per symbol — at every seed, because
/// `seed | 1` fixes the starting parity. A checker whose sampler cannot reach
/// bit 0 cannot see a bit-0 lowering defect, and this one carried a seed in its
/// certificate as if it could. The finalizer makes every output bit depend on
/// the whole state.
fn sample_stream(seed: u64) -> impl FnMut() -> u64 {
    let mut state = seed | 1;
    move || {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let z = (state ^ (state >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        let z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The sampler must be able to put BOTH values into the low bit of every
    /// symbol, on the draw schedule the checker uses (two draws per bit-vector
    /// symbol, symbols in a fixed order). Before the output mixer this was
    /// false at every seed: the first of the two draws always landed on an
    /// even LCG state, so bit 0 of every symbol was 0 on every sample, and a
    /// bit-0 lowering defect (a dropped carry out of bit 0, the LSB of a
    /// multiplier) was invisible to a check that carries a seed as evidence.
    #[test]
    fn the_sampler_reaches_both_low_bit_values_of_every_symbol() {
        for seed in [0xABCD_u64, 0x1234, 1, u64::MAX] {
            // The checker's own stream, not a copy of it: a probe over a
            // replica would stay green while the shipped sampler regressed.
            let mut next = sample_stream(seed);
            let symbols = 2usize;
            let mut low_bits_seen = vec![[false; 2]; symbols];
            let mut zero_seen = false;
            // The same sample count `tests/faithfulness.rs` configures for the
            // division test, so "never produced 0" is a statement about the
            // run that carries the seed, not about a shorter one.
            for _ in 0..1000 {
                for seen in &mut low_bits_seen {
                    let Value::Bv { value, .. } = random_value(Sort::BitVec(6), &mut next) else {
                        panic!("a bit-vector sort samples a bit-vector value");
                    };
                    seen[usize::try_from(value & 1).expect("one bit")] = true;
                    zero_seen |= value == 0;
                }
            }
            for (symbol, seen) in low_bits_seen.iter().enumerate() {
                assert!(
                    seen[0] && seen[1],
                    "seed {seed:#x}: symbol {symbol} never took both low-bit values: {seen:?}"
                );
            }
            assert!(
                zero_seen,
                "seed {seed:#x}: 2000 draws of a 6-bit symbol never produced 0 (the bvudiv totality corner)"
            );
        }
    }
}
