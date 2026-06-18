# Divisibility & the Euclidean Algorithm

> Layer 2 · structures · decidability: `computable` · axeyum theory: BV / LIA + GCD test · status: `covered`

## What it is

`a | b` ("a divides b") when `b = a·k` for some integer `k`. The **greatest
common divisor** `gcd(a, b)`, computed by the **Euclidean algorithm**, and
**Bézout's identity**: `gcd(a, b) = a·x + b·y` for some integers `x, y`. Leads to
the **unique factorization theorem** (every integer factors uniquely into primes).

## Role in the tour

The first real number-theory tool and a prerequisite for abstract algebra (the
division algorithm, Euclidean domains). Bézout's identity underpins modular
inverses and the Chinese remainder theorem.

## Prerequisites

- [Integers](../01-number-systems/integers.md)

## Unlocks

- [Modular Arithmetic & Congruences](modular-arithmetic.md)
- [Number Theory](../03-destinations/number-theory.md)

## Testable in axeyum

`computable` and **covered** by `Family::NumberTheory`. The gcd and Bézout
coefficients are *computed* (extended Euclidean algorithm) and then the identity
`a·x + b·y = gcd(a, b)` is *checked* by the solver/evaluator with the computed
coefficients as a witness — the textbook compute-and-verify pattern. Linear
Diophantine *unsolvability* is caught by the GCD divisibility test.

Example exercise (`Family::NumberTheory`): `bezout_identity(width, a, b)` —
witness `(x, y)` from extended Euclid, assert `a·x + b·y = gcd`; self-checks by
evaluation.

## Lean-horizon

Unique factorization *in general* (∀n) and its generalization to arbitrary
Euclidean/PID rings are Lean-horizon (Mathlib `EuclideanDomain`).

## References

- Hardy & Wright, *Theory of Numbers* (ch. 1–2).
- axeyum: `axeyum-scenarios::number_theory`, `prove_lia_unsat_by_gcd`.
