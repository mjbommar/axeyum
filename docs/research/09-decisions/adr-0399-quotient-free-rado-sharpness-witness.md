# ADR-0399: Quotient-free Rado sharpness witness

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.2 / R7.1.

## Context

The paper defines `u=N/b-a`, `X=N-ab+1`, `Y=1`, and `Z=au`, then proves
`a(X-Y)=bZ`. Axeyum does not yet have checked Euclidean division, and adding it
solely to spell `N/b` would violate the R4.7 dependency order. The paper first
uses only the factor fact `b | N`, so an explicit quotient witness is enough.

Connecting that witness exposed a general missing law: bounded natural
subtraction must distribute under left multiplication.

## Decision

Add the zero-axiom checked theorem

`mul_sub_left_distrib : a <= q -> b*(q-a) = b*q-b*a`.

Derive it from `sub_add_cancel`, distributivity, transported order evidence,
and additive cancellation; do not postulate multiplication monotonicity.

In the Rado integration development, admit the quotient-free theorem: from
`N=b*q` and `a<=q`, the paper definitions of `u`, `X`, `Y`, and `Z` satisfy
`a*(X-Y)=b*Z`. Keep the theorem separate from the generic Nat prelude.

## Evidence

The Nat suite checks `3*(7-2)=3*7-3*2=15` and rejects a mutation replacing
the scaled subtrahend. The Rado suite checks `(a,b,N,q)=(2,3,15,5)`, where
`(X,Y,u,Z)=(10,1,3,6)` and both equation sides reduce to 18. Dropping the
`+1` from `X` changes the target to `16=18`; the trusted gate rejects the
valid witness proof without insertion. Both environments contain zero axioms.

## Consequences

The paper's witness equation is checked without Euclidean division. The
closed-form construction of `q`, witness range bounds, divisibility/valuation,
and colour computations remain. This is not `thm:sharp` and earns no theorem
credit.
