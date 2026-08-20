# ADR-0520: Reject a supersingular decomposition of every new Carlitz layer

Status: accepted
Date: 2026-08-19
Index-summary: Use exact even-power trace divisibility to reject a blanket quadratic-Heisenberg decomposition of the new Carlitz conductor layers

## Context

ADR-0519 identifies the open connected trace with relative cohomology in the
binary Carlitz tower.  Ito--Takeuchi--Tsushima explicitly diagonalize the
quadratic Artin--Schreier curves `y^2-y=xR(x)` through Heisenberg
representations.  A tempting bridge is that every new exact-conductor Carlitz
component might decompose into supersingular factors of this kind, even though
the full tower contains an inherited nonsupersingular level-four factor.

This proposal has a sharp necessary condition.  If every Frobenius eigenvalue
of one exact-conductor component is `sqrt(2)` times a root of unity, then at
even degree `2m` its integral trace is divisible by `2^m`.

## Decision

Add `exact_conductor_supersingularity_divisibility` as a bounded exact test and
reject the blanket supersingular decomposition when its remainder is nonzero.

The operation obtains the exact conductor-layer trace from the independently
checked Hayes populations and computes its magnitude modulo `2^(degree/2)`.
A nonzero remainder is a theorem-level obstruction; a zero remainder is
explicitly inconclusive.

## Evidence

At exact conductor level ten and Frobenius degree 22, the checked trace is

```text
T_(10,22) = -5120.
```

The necessary divisor is `2^11=2048`, but the magnitude has remainder `1024`.
Therefore the entire exact level-ten component is not supersingular and cannot
be a product of only the quadratic Heisenberg factors under consideration.
The ordinary test pins this witness, a divisible inconclusive control at
`(level,degree)=(4,4)`, and rejection of odd degrees.

## Alternatives

- Finite searches for periodic normalized traces were rejected: absence of a
  period in a window would not refute supersingularity.
- Nonsupersingularity of the whole curve was insufficient because it could be
  inherited entirely from a fixed low level.  The exact-conductor witness
  closes that loophole.

## Consequences

- The Ito--Takeuchi--Tsushima quadratic decomposition cannot be imported for
  every new Carlitz layer.
- A useful Heisenberg argument would have to isolate a cancelling subquotient
  or prove a non-supersingular rank estimate for the connected sum; it cannot
  identify the full relative cohomology with supersingular quadratic pieces.
- The connected cumulant/gcd route remains the fallback if no such subquotient
  is exhibited.
