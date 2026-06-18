# Fields

> Layer 2 · structures · decidability: `bounded` · axeyum theory: LRA (ℚ) / BV (𝔽ₚ) · status: `covered`

## What it is

A commutative ring in which every nonzero element has a **multiplicative
inverse** — so you can divide. Examples: ℚ, ℝ, ℂ, and the finite fields 𝔽ₚ =
ℤ/pℤ for prime `p`.

## Role in the tour

The scalars of linear algebra and the top of the basic algebraic hierarchy
(group → ring → **field**). The two concrete fields axeyum reasons about exactly
— ℚ (via the rational simplex) and 𝔽ₚ (via modular/BV arithmetic) — make field
theory testable.

## Prerequisites

- [Rings](rings.md)
- [Rational Numbers](../01-number-systems/rationals.md) — ℚ is the first field.
- [Modular Arithmetic & Congruences](modular-arithmetic.md) — 𝔽ₚ is ℤ/pℤ.

## Unlocks

- [Linear Algebra](../03-destinations/linear-algebra.md)
- [Polynomials](polynomials.md)

## Testable in axeyum

Over ℚ the field axioms and inverse existence are LRA-checkable; over 𝔽ₚ they are
finite/BV-checkable. The defining property — every nonzero element is invertible
— is a per-element compute-and-verify check in a finite field.

Example exercise: in 𝔽₇, exhibit each nonzero element's inverse (witness table)
and verify `a·a⁻¹ = 1`; contrast with ℤ/6ℤ where `2` and `3` have no inverse
(not a field), shown by an exhaustive no-inverse check. Teaches *why prime
moduli matter*.

**Built** (`Family::Algebra`): `field_failure_even` — the claim `∃b. 2·b ≡ 1
(mod 2ʷ)` is exhaustively UNSAT (the even `2` has no inverse), proving ℤ/2ʷ is
**not a field**. The 𝔽ₚ inverse-table (SAT) and the prime-vs-composite contrast
are the next increment.

## Lean-horizon

Field extensions, Galois theory, algebraic closure, and quantification over all
fields are Lean-horizon (Mathlib `FieldTheory`).

## References

- Dummit & Foote, *Abstract Algebra* (fields).
- axeyum: `check_with_lra` (ℚ), `axeyum-bv` / modular (𝔽ₚ).
