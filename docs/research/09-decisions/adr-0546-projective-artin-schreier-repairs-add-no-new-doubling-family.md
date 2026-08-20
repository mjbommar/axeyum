# ADR-0546: Projective Artin--Schreier repairs add no new doubling family

Status: accepted
Date: 2026-08-20
Index-summary: Classify all three binary projective involutions and prove that an Artin--Schreier doubling repair is impossible, reducible, or the already known self-reciprocal cyclotomic candidate

## Context

For an odd-degree shaped irreducible `f`, the trace criterion can make
`f(x^2+x+1)` irreducible even though its coefficient in degree `2n-1` violates
the half-degree shape.  It remained possible that one of the six changes of
variable in `PGL_2(GF(2))` could move that coefficient into the allowed lower
half while preserving irreducibility.

Every such composition is invariant under `x -> x+1`.  Projective conjugacy
reduces all six repairs to outputs stabilized by one of the three binary
involutions

```text
x -> x+1,  x -> 1/x,  x -> x/(x+1).
```

## Decision

Add `characteristic_two_projective_doubling_obstruction` to the bounded native
`GF(2)[x]` layer and classify the half-shaped outputs for each involution.

For odd `n>=3`, translation invariance is impossible: the leading term forces
degree `2n-2`, above the allowed cutoff `n`, and the tail cannot cancel it.
Inversion symmetry leaves only

```text
x^(2n)+x^n+1,
```

after the square `x^(2n)+1` is removed.  This is exactly the forced shaped
self-reciprocal output already classified by ADR-0542, so it contributes no
new degree mechanism.

For the third involution, reciprocation converts invariance under
`x -> x/(x+1)` to translation invariance.  The invariant ring
`GF(2)[x^2+x]` and the coefficient gap leave only

```text
x^(2n)+(x+1)^n.
```

This polynomial is divisible by `x^2+x+1`: if `w^2+w+1=0`, then
`w+1=w^2` and the two displayed summands have the same value.  The operation
constructs this candidate by Lucas submasks and checks the division with the
bounded polynomial context.  It also constructs the inversion candidate and
requires exact equality with ADR-0542's Q-output.  Focused tests replay every
odd `3<=n<=63`, the cubic representatives, and resource declines.

## Consequences

- The familiar irreducible odd-degree Artin--Schreier composition cannot be
  turned into a new universal shaped doubling induction by a binary Mobius
  transformation.
- The sole potentially irreducible projective candidate is the existing
  `x^(2n)+x^n+1` cyclotomic/Q family; this result grants no additional degree
  coverage.
- This is a structural construction obstruction, not progress on the signed
  Hayes endpoint estimate.  The aggregate connected trace remains the proof
  frontier.
