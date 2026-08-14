# ADR-0415: Relational closed Nat intervals

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.5 / R7.1.

## Context

The proof of `thm:sharp` colours the explicit witness by placing two terms in
the endpoint shells `[1,ab]` and `[N-ab+1,N]`. Axeyum had checked order facts
for those endpoints but had no public proposition connecting both bounds to
interval membership.

## Decision

Define closed membership relationally in the zero-axiom Nat prelude:

```text
Nat.inClosedInterval lower upper value :=
  Nat.le lower value ∧ Nat.le value upper
```

Keep the definition reducible and use ordinary checked conjunction
introduction for membership proofs. This adds no interval container,
enumeration, cardinality, or decision procedure.

## Evidence

The focused prelude suite proves `3 ∈ [2,5]` from the existing order lemmas.
A negative control reuses that proof against `[2,4]`; declaration checking
rejects the changed upper endpoint without insertion. All 18 focused Nat tests
pass, the deterministic declaration census is 70, and the development declares
zero axioms.

## Consequences

R7.1 can now express the manuscript's endpoint shells without encoding
membership as an unchecked host predicate. R4.5 remains incomplete: the
partition/covering theorem and its required range splitting are still absent.
