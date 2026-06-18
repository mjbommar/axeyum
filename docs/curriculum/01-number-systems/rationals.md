# Rational Numbers

> Layer 1 · number systems · decidability: `computable` · axeyum theory: LRA (exact rationals) · status: `planned`

## What it is

Fractions `p/q` with `p, q` integers and `q ≠ 0`, identified up to common
factors (`2/4 = 1/2`) — formally, equivalence classes of integer pairs. The
rationals form the smallest **ordered field** containing ℤ.

## Role in the tour

The first field (so the first place linear algebra's scalars can live), and the
dense-but-incomplete number line whose "gaps" (like √2) motivate the reals.

## Prerequisites

- [Integers](integers.md) — rationals are built from integer pairs.

## Unlocks

- [Real Numbers](reals.md)
- [Fields](../02-structures/fields.md)

## Testable in axeyum

Linear arithmetic over the rationals is decidable *exactly* (no floating point):
axeyum's exact-rational simplex decides systems of linear equalities and
inequalities and emits **Farkas certificates** for unsatisfiability. Field
identities (`(p/q)·(q/p) = 1` for nonzero) are checkable.

Example exercise: solve a `2×2` rational linear system (SAT, with the exact
rational solution as witness), and refute an inconsistent one (`x = 1 ∧ x = 2`)
with a Farkas certificate — teaching both solving and certified impossibility.

## Lean-horizon

Quantified field theory and the construction's universal properties (Lean's
`Rat`, field-of-fractions theorems).

## References

- axeyum: `check_with_lra` (Farkas-certified), ADR-0015.
- Spivak, *Calculus* (construction of the number systems, appendix).
