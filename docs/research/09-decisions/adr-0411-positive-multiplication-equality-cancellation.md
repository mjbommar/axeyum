# ADR-0411: Positive multiplication equality cancellation

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.2 / R4.3 / R7.1.

## Context

The paper proves that its witness has valuation exactly two by exhibiting two
factors of `a` and refuting a third. Cancelling the common positive square from
a hypothetical third-factor equality requires equality cancellation, while the
prelude previously exposed only order reflection.

## Decision

Add the checked theorem

```text
mul_left_cancel_of_pos : 1<=c -> c*a=c*b -> a=b.
```

Transport reflexive order along the equality in both directions, reflect both
bounds through the proof-positive factor using ADR-0407, and combine the
results with ADR-0410's antisymmetry.

## Evidence

The positive test cancels a factor of three from a concrete product equality.
NC28 changes the resulting right endpoint; declaration checking rejects it
without insertion. The deterministic inventory now contains 56 theorems and
8 definitions, with zero axioms.

## Consequences

The valuation development can reduce a hypothetical `a^3 | Z` witness to the
remaining claim `a | u'`. The next dependency is the constructive
nondivisibility proof for the closed-form `u' = 1 + a*t` shape.
