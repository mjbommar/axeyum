# ADR-0424: Relational Nat Euclidean strict adjunction

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.7.

## Context

ADR-0423 supplies the floor-facing equivalence `d*s <= n iff s <= q` for a
checked decomposition. Ceiling bounds and strict multiplicative estimates need
its order-dual interface rather than ad hoc successor manipulation in every
consumer.

This distinction mattered in the Rado shell-gap proof, where integral
rounding—not a real-number estimate—carried the argument. The broadly reusable
lesson is to expose both adjunction directions while keeping the quotient a
proof witness.

## Decision

Add the zero-axiom theorem

```text
div_mod_lt_mul_iff : divMod d n q r -> (n < d*s iff q < s)
```

If `s <= q`, multiplication monotonicity and `d*q <= n` contradict `n<d*s`.
If `q<s`, then `d*(succ q) <= d*s`, and the strict floor upper bound proves
`n<d*s`. Constructive totality handles the comparison; no decidability,
positivity premise, or host arithmetic is introduced.

## Evidence

The decomposition `5 = 2*2+1` exercises the theorem at candidate `3`. NC43
changes only the quotient lower endpoint and the trusted declaration gate
rejects it without insertion. All 19 focused Nat tests pass, the deterministic
census is 81 definitions/theorems, and the prelude declares zero axioms.

## Consequences

Relational Euclidean division now exposes matching weak-floor and
strict-ceiling adjunctions. Exact-divisibility and zero-remainder
characterizations can build on this complete order surface rather than
duplicating quotient comparison arguments.
