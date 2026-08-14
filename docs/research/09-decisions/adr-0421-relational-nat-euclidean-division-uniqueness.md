# ADR-0421: Relational Nat Euclidean division uniqueness

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.7.

## Context

ADR-0419 constructively produces a quotient and bounded remainder, but
existence alone does not make those witnesses canonical. Number-theoretic
algorithms and rounding arguments need to replace independently obtained
decompositions without trusting host-language division.

## Decision

Add the zero-axiom theorem

```text
div_mod_unique :
  divMod d n q1 r1 -> divMod d n q2 r2 -> q1=q2 and r1=r2
```

No separate positivity premise is required: either relation already contains
`r < d`, which is uninhabited when `d = 0`.

The proof compares `q1` and `q2` using constructive totality. In either strict
branch, remainder boundedness and multiplication monotonicity make one
reconstruction strictly smaller than the other; their shared dividend then
contradicts strict irreflexivity. Quotient equality transports through
multiplication, and additive cancellation proves remainder equality.

## Evidence

The concrete decomposition `5 = 2*2+1` exercises the theorem. NC40 changes
only the claimed unique remainder and the trusted declaration gate rejects it
without insertion. All 19 focused Nat tests pass, the deterministic census is
78 definitions/theorems, and the prelude still declares zero axioms.

## Consequences

Relational division now has a constructive existence-and-uniqueness contract
independent of executable arithmetic. R4.7 still needs consumer-facing
quotient/remainder order and rounding lemmas before the paper's integrality
step can be credited.
