# ADR-0405: Positive multiplication reflects Nat order

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.1 / R4.2 / R7.1.

## Context

The paper's exact `Z<=N` criterion scales an inequality by `b` and later
cancels that factor under `b>=1`. Forward multiplication monotonicity landed
under ADR-0401, but its converse for positive factors was still missing. This
is also one of the cancellation gaps named by R4.2.

## Decision

Add checked theorems

```text
not_succ_le_zero             : Not (succ n <= 0)
le_of_mul_le_mul_left_succ   : (succ c)*a <= (succ c)*b -> a <= b.
```

Prove successor exclusion by eliminating a hypothetical `Le` derivation into
a Nat-indexed family that is `False` at zero and `True` at successors. Prove
multiplicative reflection by induction on both compared values. The impossible
successor/zero branch uses that exclusion; the successor/successor branch
exposes the common positive addend and invokes ADR-0404's additive reflection.

## Evidence

The downstream test reflects `3*2<=3*5` back to `2<=5` and infers the
successor-exclusion theorem. NC23 changes the reflected lower endpoint; the
trusted gate rejects it without insertion. The deterministic inventory now
contains 49 theorems and 8 definitions, with zero axioms.

## Consequences

The zero-axiom Nat library can cancel any multiplication factor presented as a
successor. A `1<=b` proof can expose exactly that representation through
ADR-0404's additive witness, enabling the exact scaled Rado range equivalence.
