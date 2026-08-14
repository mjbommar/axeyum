# ADR-0406: Truncated subtraction order adjunction

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.1 / R4.2 / R7.1.

## Context

The paper rewrites the exact Rado witness range through inequalities of the
form `x-y<=z` and `x<=z+y`. Nat subtraction is truncated, so that rewrite
cannot be treated as ring normalization: both `y<=x` and `x<=y` must be
checked, and the latter branch must account for `x-y=0`.

## Decision

Add checked theorems

```text
add_le_add_right          : a<=b -> a+c<=b+c
le_of_add_le_add_right    : a+c<=b+c -> a<=b
sub_eq_zero_of_le         : a<=b -> a-b=0
sub_le_iff_le_add         : (x-y<=z) <-> (x<=z+y).
```

Derive the right-addition laws from the proved left-addition laws and
commutativity. Prove subtraction-to-zero by eliminating the order derivation.
Prove the adjunction by totality: restore the difference when `y<=x`, and use
truncation plus transitivity when `x<=y`.

## Evidence

The downstream test infers right-additive monotonicity and reflection,
subtraction-to-zero, and the full adjunction. NC24 reverses the subtraction
operands and NC25 changes the adjunction's upper bound; the trusted gate rejects
both without insertion. The deterministic inventory now contains 53 theorems
and 8 definitions, with zero axioms.

## Consequences

The exact paper inequality can now cross the Nat subtraction boundary without
an axiom or an implicit integer coercion. Positive-factor cancellation and
the remaining multiplication/commutation transports still have to be composed
in the dedicated Rado theorem.
