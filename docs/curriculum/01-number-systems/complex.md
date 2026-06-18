# Complex Numbers

> Layer 1 · number systems · decidability: `bounded` · axeyum theory: NRA over pairs · status: `lean-horizon`

## What it is

Numbers `a + bi` with `i² = −1`, modeled as pairs of reals with a twisted
multiplication. The complex field is **algebraically closed** (the fundamental
theorem of algebra: every non-constant polynomial has a root).

## Role in the tour

An optional but illuminating side-trip: it completes the algebraic picture and
appears in linear algebra (eigenvalues) and analysis (complex analysis). Included
for completeness of the number-systems layer.

## Prerequisites

- [Real Numbers](reals.md)

## Unlocks

(Terminal optional node.)

## Testable in axeyum

Modeling `ℂ` as pairs of reals, **algebraic identities** are polynomial
identities over ℝ and so fall in the NRA fragment: e.g. `|z·w| = |z|·|w|`
expressed via real and imaginary parts becomes a polynomial identity in four
real variables, checkable by NRA.

Example exercise: `(a + bi)(a − bi) = a² + b²` as a pair-of-reals identity —
a checkable NRA fact teaching the modulus.

## Lean-horizon

The fundamental theorem of algebra, complex analysis (holomorphy, contour
integration), and anything quantifying over all polynomials are Lean-horizon.

## References

- Needham, *Visual Complex Analysis*.
- axeyum: NRA (ADR-0024).
