# ADR-0414: Closed-form Rado witness valuation

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.3 / R4.6 / R4.9 / R7.1.

## Context

The proof of `thm:sharp` compresses its valuation argument into `u'=1+a*t`,
therefore `a` does not divide `u'`, and consequently `v_a(Z)=2`. The checked
closed form uses a shifted finite sum and `Z=a*(q-a)`, so every identification
hidden by that prose must be represented explicitly.

## Decision

Add a paper-shaped checked theorem proving

```text
2<=a -> valuationAt a Z 2
```

for the existing closed-form witness. Use `mul_sumRange_pow` to factor the
shifted sum by `a`; factor the successor power with `pow_succ`; distribute to
write the entire inner tail as `a*t`; invoke ADR-0412 for nondivisibility and
ADR-0413 for exact valuation; finally prove `q-a=a*u'` by subtraction
restoration and transport the result to the manuscript's `Z=a*(q-a)`.

## Evidence

The `k=3` empty-range corner checks at `a=2,b=3`, where `Z=12` has exact
base-two valuation two. A negative control changes the exponent to one;
declaration checking rejects it without insertion. The focused Rado module now
contains 13 passing tests and the development declares zero axioms.

## Consequences

The witness equation, all range facts including the exact biconditional, and
the exact valuation of `Z` are checked. The remaining `thm:sharp` work is the
shell-colour layer: interval membership and the unit/valuation branches of the
colouring definition for `X`, `Y`, and `Z`.
