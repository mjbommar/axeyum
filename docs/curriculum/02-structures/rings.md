# Rings

> Layer 2 · structures · decidability: `bounded` · axeyum theory: BV / enumeration · status: `covered`

## What it is

A set with **two** operations — addition (an abelian group) and multiplication
(associative) — linked by **distributivity**. Examples: the integers ℤ,
polynomials, `n×n` matrices, ℤ/nℤ.

## Role in the tour

The structure where number theory and linear algebra meet abstraction: ℤ is the
motivating ring, matrices are a noncommutative ring, ℤ/nℤ a finite ring. The
middle of the algebraic hierarchy (group → **ring** → field).

## Prerequisites

- [Groups](groups.md) — a ring is an abelian group under +.
- [Integers](../01-number-systems/integers.md) — the prototypical ring.

## Unlocks

- [Fields](fields.md)
- [Polynomials](polynomials.md)

## Testable in axeyum

Finite rings (e.g. ℤ/nℤ) make the ring axioms — distributivity especially —
decidable finite checks. Over `BitVec(n)` the ring axioms of ℤ/2ⁿℤ hold and are
exhaustively checkable; distributivity is the same `x·(y+z) = x·y + x·z`
identity already in the `arithmetic` family.

Example exercise: verify the ring axioms of ℤ/2ⁿℤ over `BitVec(n)`
(distributivity refuted-by-negation exhaustively); exhibit a zero-divisor
(`2·(2ⁿ⁻¹) = 0`) as a witness, teaching that ℤ/nℤ need not be an integral domain.

**Built** (`Family::Algebra`): `zero_divisor` — a SAT witness (`a=2, b=2ⁿ⁻¹`,
both nonzero, `a·b≡0`) showing ℤ/2ⁿ is a ring but **not an integral domain**.
(Ring distributivity itself is already exercised by `Family::Arithmetic`'s
`distributivity_identity`.)

## Lean-horizon

Ideal theory, Noetherian/PID/UFD structure, and quantification over all rings
are Lean-horizon (Mathlib `RingTheory`).

## References

- Dummit & Foote, *Abstract Algebra* (rings).
- axeyum: `axeyum-bv`, the `arithmetic`/`identity` families.
