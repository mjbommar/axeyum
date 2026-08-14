# ADR-0423: Relational Nat Euclidean floor adjunction

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.7.

## Context

Floor bounds characterize a checked quotient geometrically, but consumers
still need the order interface that makes integrality useful: multiplication
by the divisor on one side of an inequality must correspond to comparison
with the quotient on the other.

This is the general lesson from the Rado shell-gap argument. A real-valued
bound was too weak; the proof needed an integer candidate to compare against a
floor. The library boundary is an order adjunction, not paper-specific
rounding algebra.

## Decision

Add the zero-axiom theorem

```text
div_mod_mul_le_iff : divMod d n q r -> (d*s <= n iff s <= q)
```

For the reverse implication, multiply `s <= q` monotonically and compose with
`d*q <= n`. For the forward implication, totality reduces the only difficult
case to `q<s`; then `n<d*(succ q)<=d*s<=n` contradicts strict irreflexivity.

Do not require a separate positivity hypothesis. A valid relation already
provides `r<d`, and its derived strict upper floor bound is exactly what the
proof uses.

## Evidence

The decomposition `5 = 2*2+1` exercises the equivalence at candidate `2`.
NC42 changes only the quotient endpoint and the trusted declaration gate
rejects it without insertion. All 19 focused Nat tests pass, the deterministic
census is 80 definitions/theorems, and the prelude declares zero axioms.

## Consequences

Checked relational division now supports the standard floor adjunction needed
by integral rounding, bounded algorithms, and number-theoretic estimates. The
next layer can derive exact-division and ceiling corollaries without exposing
an executable quotient or specializing to the motivating paper.
