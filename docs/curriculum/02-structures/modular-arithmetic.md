# Modular Arithmetic & Congruences

> Layer 2 · structures · decidability: `bounded` · axeyum theory: BV / LIA · status: `covered`

## What it is

Arithmetic in ℤ/nℤ: `a ≡ b (mod n)` when `n | (a − b)`. The residues
{0, …, n−1} form a ring under + and ×; when `n` is prime they form a **field**.
Key results: modular **inverses** (exist iff `gcd(a, n) = 1`), **Fermat's little
theorem** (`aᵖ⁻¹ ≡ 1 (mod p)`), and the **Chinese remainder theorem**.

## Role in the tour

The computational heart of number theory and cryptography, and the bridge from
divisibility to finite fields. The "clock arithmetic" that makes finite,
exhaustively-checkable instances of deep theorems.

## Prerequisites

- [Divisibility & the Euclidean Algorithm](divisibility-and-euclid.md)

## Unlocks

- [Number Theory](../03-destinations/number-theory.md)
- [Fields](fields.md) — ℤ/pℤ is the prototype finite field.

## Testable in axeyum

Modular arithmetic mod `2ⁿ` is **exactly** bit-vector arithmetic, so congruence
identities are BV identities, exhaustively checkable; mod general `n` maps to LIA
with a divisibility constraint. Modular **inverses** are compute-and-verify
(`a·a⁻¹ ≡ 1`).

Example exercises (`Family::NumberTheory`): `modular_inverse(width, a)` for odd
`a` (invertible mod `2ⁿ`), witness = the inverse; `square_parity` (`x² ≡ x
(mod 2)`) refuted-by-negation exhaustively.

## Lean-horizon

Fermat's little theorem / Euler's theorem *as universal statements over all `a`*
(general `p`) need the group-order argument — Lean-horizon, though fixed-`p`
instances are checkable.

## References

- Hardy & Wright, *Theory of Numbers*.
- axeyum: `axeyum-scenarios::number_theory`, `axeyum-bv`.
