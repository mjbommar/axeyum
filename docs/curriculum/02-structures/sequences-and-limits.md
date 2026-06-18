# Sequences & Limits

> Layer 2 · structures · decidability: `bounded` · axeyum theory: LRA / NRA · status: `lean-horizon`

## What it is

A **sequence** assigns a real number to each natural; it **converges** to `L` if
its terms get and stay arbitrarily close to `L` — the **ε–N** definition:
`∀ε>0 ∃N ∀n>N. |aₙ − L| < ε`. Limits underpin continuity, derivatives, and
integrals.

## Role in the tour

The conceptual core of calculus and the first essential use of nested
quantifiers over the reals — the place where the gap between "computable" and
"provable" becomes vivid.

## Prerequisites

- [Real Numbers](../01-number-systems/reals.md) — limits require completeness.

## Unlocks

- [Calculus](../03-destinations/calculus.md)

## Testable in axeyum

Only fragments: a **specific algebraic limit value** can be checked by verifying
the closed form (e.g. a geometric-series partial sum identity is a polynomial/
rational identity over NRA), and **monotonicity/boundedness of a concrete
sequence** on a range is an LRA/NRA check. The ε–N definition itself — with its
`∀ε ∃N ∀n` alternation over infinite domains — is not an SMT query.

Example exercise: verify the geometric partial-sum identity
`(1 − r)·∑₀ⁿ rᵏ = 1 − rⁿ⁺¹` at fixed `n` (a polynomial identity, NRA);
verify a sequence is increasing on `[0, k]` by checking `aᵢ < aᵢ₊₁` pointwise.

## Lean-horizon

The ε–N/ε–δ machinery, convergence theorems (monotone convergence,
Bolzano–Weierstrass), and Cauchy completeness are the substance of real analysis
and are Lean-horizon (Mathlib `Analysis`). This node is intentionally marked
`lean-horizon`.

## References

- Rudin, *Principles of Mathematical Analysis* (ch. 3).
- axeyum: NRA / LRA; the example-suites note's "real analysis" row.
