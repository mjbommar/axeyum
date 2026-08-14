# ADR-0416: Closed-form Rado witness colour two

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.5 / R4.9 / R7.1.

## Context

The final paragraph of `thm:sharp` says `X` and `Y` are units in the two
intervals of `Sh_2`, while `Z` has exact valuation two. Those statements were
available separately, but there was no checked colour relation joining domain
membership, the shell-unit branch, and the valuation branch.

## Decision

Represent the paper-specific fragment by reducible relations:

```text
shellTwoMember N ab j := j in [1,ab] or j in [N-ab+1,N]
colourTwoAt a N ab j :=
  j in [1,N] and (valuationAt a j 2 or (not (a divides j) and shellTwoMember N ab j))
```

Prove that the closed-form `X`, `Y`, and `Z` all satisfy `colourTwoAt` from
`2<=a`, `1<=b`, and the manuscript's explicit `Z<=N` guard. Derive the unit
fact for `X` by checking `N-ab=a*(b*inner)` and transporting constructive
one-plus-multiple nondivisibility.

## Evidence

At the empty-range corner `a=2,b=3,n=0`, the theorem checks colour two for
`X=19`, `Y=1`, and `Z=12` in `[1,24]`. A negative control changes the shell
width from six to five, moving the right interval endpoint; the kernel rejects
the declaration without insertion. All 15 focused Rado factorization tests
pass and the development declares zero axioms.

## Consequences

Every mathematical step in the explicit monochromatic witness of `thm:sharp`
is now represented by checked terms: construction, equation, ranges, exact
valuation, shell membership, unit facts, and colour two. This is not yet a
global shell colouring: well-definedness and partition/covering remain R4.5
work, and the theorem deliberately requires `Z<=N` exactly as the paper does.
