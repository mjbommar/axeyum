# ADR-0431: Additive closure of Nat congruence

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.4.

## Context

ADR-0430 proves preservation beneath a common left addition. General modular
arithmetic also needs a common right shift and addition of two independently
congruent pairs. Reopening four balanced-witness existentials for the pairwise
law would duplicate algebra and obscure which earlier contracts it depends on.

## Decision

Add the zero-axiom theorems

```text
mod_eq_add_right : modEq d a b -> modEq d (a+c) (b+c)
mod_eq_add       : modEq d a b -> modEq d c e -> modEq d (a+c) (b+e).
```

Derive right-addition compatibility by applying ADR-0430 and transporting both
endpoints across checked addition commutativity. Derive pairwise addition by
right-shifting the first relation, left-shifting the second, and composing them
with checked congruence transitivity.

This proof-directed composition is preferred to a second hand-expanded witness
calculation: it validates that the public equivalence and left-addition laws are
usable as a coherent downstream API.

## Evidence

The concrete relation `2 ≡ 7 (mod 5)` survives a common right shift by three.
Together with `3 ≡ 8 (mod 5)`, pairwise addition proves
`2+3 ≡ 7+8 (mod 5)`. NC50 changes the common right shift and NC51 changes one
pairwise endpoint; the trusted gate rejects both. All 20 focused Nat tests pass,
including 51 negative controls, the deterministic 90-definition/theorem census,
and the zero-axiom audit.

## Consequences

`Nat.modEq` is now an additive congruence relation, not only an equivalence
relation. Multiplication compatibility, divisibility links, and remainder
characterizations remain explicit follow-up work.
