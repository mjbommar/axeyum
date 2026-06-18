# Calculus

> Layer 3 · destinations · decidability: `bounded` · axeyum theory: NRA · status: `lean-horizon`

## What it is

The mathematics of change and accumulation: **limits**, **continuity**,
**derivatives** (instantaneous rates), **integrals** (accumulated area), and
**series**. Built on the real numbers and the limit concept.

## Role in the tour

The analytic destination, and the one most dependent on genuinely infinitary
machinery (ε–δ limits) — so the most `lean-horizon` of the three, but with real
decidable islands worth teaching and testing.

## Prerequisites

- [Real Numbers](../01-number-systems/reals.md)
- [Sequences & Limits](../02-structures/sequences-and-limits.md)
- [Polynomials](../02-structures/polynomials.md)

## Unlocks

(Destination.)

## Testable in axeyum

The decidable islands: **symbolic differentiation as computation** — compute a
derivative by the rules, then *verify* it (e.g. check the product rule
`(f·g)′ = f′g + fg′` on polynomial instances as an NRA identity); **polynomial/
rational identities**; and **RCF inequalities** (AM–GM, Cauchy–Schwarz at fixed
arity; monotonicity facts) decided by NRA — the same real-closed-field reasoning
as the geometry suite.

Example exercise: verify `d/dx (x³) = 3x²` by checking the limit-free polynomial
identity the power rule predicts; prove `x² + y² ≥ 2xy` over NRA. These teach
calculus's *algebra* with machine-checked certainty, while flagging the limit
layer as out of reach.

## Lean-horizon

The definitions and theorems built on ε–δ — continuity, differentiability, the
mean value theorem, the fundamental theorem of calculus, convergence of series —
are Lean-horizon (Mathlib `Analysis`); only the algebraic shadow is decidable.

## References

- Spivak, *Calculus*; Rudin, *Principles of Mathematical Analysis*.
- axeyum: NRA (ADR-0024); MetiTarski (RCF inequalities) as the yardstick.
