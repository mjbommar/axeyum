# ADR-0430: Left addition preserves Nat congruence

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.4.

## Context

ADR-0428 establishes `Nat.modEq` as an equivalence relation. A useful
congruence library must also show that arithmetic contexts preserve the
relation. Addition is the first dependency for residue-class algebra and later
number-theory algorithms.

## Decision

Add the zero-axiom theorem

```text
mod_eq_add_left : modEq d a b -> modEq d (c+a) (c+b).
```

Eliminate the balanced witnesses and reuse them unchanged. The required
equation is obtained by reassociating `(c+a)+d*u`, transporting the original
equality under `c+_`, and reassociating back at `(c+b)+d*v`.

Keep this law separate from right-addition and pairwise-addition closure so
each direction has an explicit proof and mutation boundary.

## Evidence

The checked concrete relation `2 ≡ 7 (mod 5)` shifts by three to prove
`5 ≡ 10 (mod 5)`. NC49 changes only the left shift in the conclusion and the
trusted declaration gate rejects it. All 20 focused Nat tests pass, including
49 negative controls, the deterministic 88-definition/theorem census, and the
zero-axiom audit.

## Consequences

Congruent naturals may now be substituted beneath a common left addition.
Right-addition, pairwise addition, multiplication compatibility, divisibility
links, and remainder characterizations remain follow-up work.
