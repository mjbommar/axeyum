# ADR-0418: Constructive strict-or-equal order decomposition

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.1 / R4.7.

## Context

A zero-axiom Euclidean-division relation can be populated by induction on the
dividend: increment the remainder while it stays below the positive divisor,
and carry into the quotient when it reaches the divisor. The existing order
fragment could prove a bound but could not constructively distinguish its
strict and equality cases.

## Decision

Add the proved prelude theorem

```text
Nat.lt_or_eq_of_le : forall a b, a <= b -> a < b or a = b.
```

Eliminate the `Nat.le` derivation directly. Its reflexive constructor selects
equality; its step constructor lifts the previous bound with
`le_succ_succ` and selects strict order. No decidability or classical logic is
introduced.

## Evidence

The positive control decomposes `2<=5`. A negative control changes only the
lower endpoint from two to three, and declaration checking rejects it without
insertion. All 18 focused Nat tests pass, the deterministic declaration census
is 71, and the prelude declares zero axioms.

## Consequences

This fills a general order-library gap and supplies the exact branch needed by
dividend-inductive quotient/remainder existence. R4.7 remains incomplete until
the relational decomposition, existence, and uniqueness properties land.
