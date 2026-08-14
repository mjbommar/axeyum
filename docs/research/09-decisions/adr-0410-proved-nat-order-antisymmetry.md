# ADR-0410: Proved Nat order antisymmetry

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.1 / R7.1.

## Context

The remaining colour proof needs to turn two reflected inequalities into an
equality when cancelling positive factors from a divisibility witness. The Nat
prelude had totality and reflection, but R4.1 still correctly listed
antisymmetry as absent.

## Decision

Add the checked theorem

```text
le_antisymm : a<=b -> b<=a -> a=b.
```

Induct over both endpoints. Eliminate mixed zero/successor branches with the
proved impossibility of a successor below zero. In the successor/successor
branch, invert both bounds, apply the induction hypothesis, and lift equality
through `succ`.

## Evidence

The positive test equates `2+3` and `5` from bounds in both directions. NC27
changes one equality endpoint; declaration checking rejects it without
insertion. The deterministic inventory now contains 55 theorems and 8
definitions, with zero axioms.

## Consequences

R4.1's antisymmetry gap is closed. Together with proof-positive
multiplicative order reflection, the prelude can now support checked positive
multiplication equality cancellation for the valuation/nondivisibility layer.
