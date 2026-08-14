# ADR-0407: Proof-directed positive multiplication reflection

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.1 / R4.2 / R7.1.

## Context

ADR-0405 cancels a multiplication factor that is syntactically a successor.
The Rado theorem instead receives the mathematical hypothesis `1<=b`; its
proof should not depend on the expression chosen to represent `b`.

## Decision

Add the checked theorem

```text
le_of_mul_le_mul_left : 1<=c -> c*a<=c*b -> a<=b.
```

Use the additive witness exposed by `le_dest` to write `c=1+k`, prove that
`1+k=succ k`, transport both scaled endpoints, and invoke ADR-0405's
successor-factor theorem.

## Evidence

The positive control cancels a factor of three using a separately constructed
proof of `1<=3`. NC26 changes the reflected lower endpoint; the trusted gate
rejects it without insertion. The deterministic inventory now contains 54
theorems and 8 definitions, with zero axioms.

## Consequences

The exact Rado range proof can scale and cancel by `b` using precisely the
paper hypothesis `1<=b`. No syntactic positivity convention crosses into the
paper-shaped development.
