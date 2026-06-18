# Polynomials

> Layer 2 · structures · decidability: `computable` · axeyum theory: BV (fixed-degree) / NRA · status: `covered`

## What it is

Formal expressions `aₙxⁿ + … + a₁x + a₀` over a ring/field, with addition and
multiplication. Key notions: **degree**, **roots**, **factorization**, and
polynomial identities.

## Role in the tour

The bridge from algebra to analysis and linear algebra: derivatives act on
polynomials, characteristic polynomials give eigenvalues, and polynomial
identities are the decidable core of real-closed-field reasoning.

## Prerequisites

- [Rings](rings.md) — polynomials form a ring.
- [Fields](fields.md) — coefficients/roots over a field.

## Unlocks

- [Calculus](../03-destinations/calculus.md)
- [Linear Algebra](../03-destinations/linear-algebra.md)

## Testable in axeyum

**Fixed-degree polynomial identities** are decidable: expand both sides and
compare, or refute the negated equality over NRA / exact rational arithmetic.
Evaluating a polynomial at a point and checking a claimed root are
compute-and-verify.

Example exercise: the identity `(x + 1)² = x² + 2x + 1` and the difference of
squares `x² − y² = (x − y)(x + y)`, refuted-by-negation over NRA; verify a
claimed root of `x² − 5x + 6` (namely `2`, `3`) by evaluation.

**Built** (`Family::Polynomial`, over fixed-degree `BitVec` polynomials,
exhaustive/witness self-checks): `binomial_square` ((x+y)²=x²+2xy+y²),
`difference_of_squares` (x²−y²=(x−y)(x+y)) as exhaustive UNSAT of the negation,
and `quadratic_root` (x²−5x+6=0 with the root `x=2` as witness). The NRA variants
over ℚ (fixed-degree identities, root isolation) are the next increment.

## Lean-horizon

The fundamental theorem of algebra, irreducibility/factorization over general
fields, and quantification over all polynomials are Lean-horizon.

## References

- axeyum: NRA (ADR-0024), exact-rational evaluator.
- Dummit & Foote, *Abstract Algebra* (polynomial rings).
