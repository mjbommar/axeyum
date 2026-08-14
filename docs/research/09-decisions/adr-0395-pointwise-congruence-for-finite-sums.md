# ADR-0395: Pointwise congruence for finite sums

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.6 / R7.1.

## Context

ADR-0394 moves a scalar inside `sumRange`. The Rado sharpness factorization
then needs to rewrite every scaled power using `mul_comm` and `pow_succ`.
Re-proving the finite induction at each pointwise rewrite would duplicate a
general mathematical rule. Assuming function extensionality would also widen
the logical surface beyond what finite sums require.

## Decision

Add the zero-axiom checked theorem

`Nat.sumRange_congr : forall f g n,
  (forall i, f i = g i) -> sumRange f n = sumRange g n`.

Prove it by induction on `n`: the empty sums reduce to zero, and the successor
case transports the induction hypothesis through the prior sum and the
pointwise hypothesis through the appended summand. Require only pointwise
equality; do not add function extensionality.

## Evidence

The focused Nat suite lifts the checked theorem `zero_add i : 0+i=i` through
four summands. A mutation control assigns the valid range-two proof to the
inferred range-three proposition and requires trusted-gate rejection without
insertion. The declaration inventory, deterministic rebuild, and zero-axiom
walk cover the package boundary.

## Consequences

Pointwise arithmetic equalities can now rewrite finite sums constructively.
Together with ADR-0394, this supports the scaled-power normalization in the
exact `thm:sharp` factorization. Range splitting and other finite-sum algebra
remain separate checked increments.
