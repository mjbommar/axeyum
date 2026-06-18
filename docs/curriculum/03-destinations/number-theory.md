# Number Theory

> Layer 3 · destinations · decidability: `bounded` · axeyum theory: BV / LIA · status: `covered`

## What it is

The study of the integers: **primes** and factorization, **congruences**,
**Diophantine equations** (integer solutions to polynomial equations), and
landmark theorems — infinitude of primes, the fundamental theorem of arithmetic,
Fermat's little theorem, Euler's theorem, the Chinese remainder theorem.

## Role in the tour

A destination, and the most *decidable-friendly* of the three: its
computational core (gcd, modular arithmetic, linear Diophantine) is exactly what
axeyum decides today, so it is the first destination with a self-checking
exercise family.

## Prerequisites

- [Divisibility & the Euclidean Algorithm](../02-structures/divisibility-and-euclid.md)
- [Modular Arithmetic & Congruences](../02-structures/modular-arithmetic.md)
- [Mathematical Induction](../00-foundations/induction.md)
- [Counting & Combinatorics](../02-structures/counting.md)

## Unlocks

(Destination.)

## Testable in axeyum

**Covered** by `Family::NumberTheory`. The bounded/computable core self-checks
oracle-free: Bézout's identity (witness from extended Euclid), modular inverses,
parity facts, and linear Diophantine (un)solvability (GCD test). Bounded
instances of the famous theorems — Fermat's little theorem at a fixed prime,
factorization of a fixed `n` — are checkable by computation + verification.

Example exercises (`Family::NumberTheory`):
- `bezout_identity(w, a, b)` — `a·x + b·y = gcd(a,b)`, witnessed.
- `modular_inverse(w, a)` — `a·a⁻¹ ≡ 1 (mod 2ʷ)`, witnessed.
- `consecutive_product_even(w)` — `k·(k+1) ≡ 0 (mod 2)`, exhaustive `unsat` of the negation.
- `square_parity(w)` — `x² ≡ x (mod 2)`, exhaustive.

## Lean-horizon

The universal theorems — *infinitely many primes*, FTA in general, Fermat/Euler
for all `a`, quadratic reciprocity — require induction/quantifiers and are
Lean-horizon (Mathlib `NumberTheory`); axeyum certifies their bounded instances.

## References

- Hardy & Wright, *An Introduction to the Theory of Numbers*.
- axeyum: `axeyum-scenarios::number_theory`, `prove_lia_unsat_by_gcd`.
