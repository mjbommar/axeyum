# ADR-0409: Exact Rado witness range criterion

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.1 / R4.2 / R7.1.

## Context

The paper's final witness-range obligation is the biconditional

```text
Z<=N  <->  N(a-b)<=a^2*b.
```

Its prose uses signed arithmetic and notes that the left side of the second
inequality is nonpositive when `b>a`. The zero-axiom development represents
that case with truncated Nat subtraction, so the proof must make the signed
case split explicit rather than apply unconditional ring normalization.

## Decision

Add a checked generic criterion under `N=b*q`, `a<=q`, and `1<=b`, then
specialize it to the exact closed-form witness used by `thm:sharp`.

For `a<=b`, prove `a-b=0`, establish both sides directly, and package the
biconditional. For `b<=a`, reproduce the manuscript chain: scale `Z<=N` by
positive `b`, rewrite `bZ=aN-a^2b`, apply subtraction/order adjunction,
commute the products and sum, rewrite `N(a-b)=Na-Nb`, and reverse every step.

## Evidence

The trusted kernel admits applications in both branches and admits the
closed-form specialization at the `k=3` empty-range corner. The development's
environment contains zero axioms. A negative control changes the `a^2*b`
endpoint; declaration checking rejects it without insertion. The focused
Rado module has 11 passing tests.

## Consequences

The complete arithmetic and range portion of the paper's explicit sharpness
witness is now represented by checked zero-axiom declarations. Finishing
`thm:sharp` next requires the colour/shell argument that uses the established
witness equation, valuation facts, and range criterion.
