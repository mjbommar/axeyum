# ADR-0417: Checked Rado sharpness certificate

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.5 / R4.6 / R4.9 / R7.1.

## Context

The checked development had proved each arithmetic and colour component of
`thm:sharp`, but consumers still had to assemble several independent theorem
names. That made it easy to overstate what was checked or omit the paper's
explicit `Z<=N` guard.

## Decision

Publish one zero-axiom certificate theorem for the closed-form witness. From
`2<=a` and `1<=b`, it conjoins:

- `a*(X-Y)=b*Z`;
- `X,Y` in `[1,N]`;
- `Z<=N` iff `N*(a-b)<=a^2*b`; and
- `Z<=N` implies all three terms satisfy the checked colour-two relation.

Do not encode the manuscript's global colouring or Ramsey-number conclusion
until the missing partition/well-definedness library exists.

## Evidence

The `a=2,b=3,n=0` empty-range instance checks the complete certificate. An
application mutation substitutes a `2<=a` proof for the required `1<=b`
premise and is rejected. All 17 focused Rado factorization tests pass and the
development declares zero axioms.

## Consequences

The current kernel can cite one exact artifact for every presently expressible
claim in the constructive core of `thm:sharp`, without claiming the absent
global theorem surface. Further work returns to reusable R4.7--R4.9 division,
valuation, and number-theory infrastructure rather than adding more
paper-specific wrappers.
