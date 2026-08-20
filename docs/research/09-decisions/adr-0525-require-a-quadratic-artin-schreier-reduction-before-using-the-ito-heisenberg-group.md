# ADR-0525: Require a quadratic Artin--Schreier reduction before using the Ito Heisenberg group

Status: accepted
Date: 2026-08-19
Index-summary: Do not import the characteristic-two Heisenberg construction until the connected phase is reduced to a linearized quadratic Artin--Schreier form

## Context

The connected dyadic/Witt experiment suggested comparing its commutator rank
with Ito--Takeuchi--Tsushima's characteristic-two Heisenberg construction.  An
equation-level audit of [their source](https://arxiv.org/abs/2505.22036) shows
that the construction begins with an additive linearized polynomial

```text
R(x)=sum_i a_i x^(p^i)
```

and the quadratic Artin--Schreier curve `y^p-y=xR(x)`.  Their two-variable
polynomial `f_R` is defined by the exact coboundary equation

```text
f_R(x,y)^p-f_R(x,y)
  = -x^(p^e) E_R(y) + xR(y) + yR(x).
```

Only after this identity is established do they define

```text
(a,b)(a',b')=(a+a', b+b'+f_R(a,a')),
[g,g']=(0,f_R(a,a')-f_R(a',a)),
```

and prove that the induced commutator form on `ker E_R` is nondegenerate.
Their length-two Witt group describes maximal abelian subgroups of this
already-quadratic Heisenberg group; it does not turn an arbitrary eighth-root
phase into a quadratic one.

Axeyum's exact stopping tests rule out that premise for the raw Lemire
correlation.  In the pinned `(ell,k,d)=(9,11,8)` row, 2,297 affine fibres are
nonquadratic and reach Boolean support degree seven; zero of 18,884 fibres are
generalized bent.  Pairwise second-trace differences also contain distinct
phase-trivial rank-zero forms.  The projection-preserving joined extension is
separately refuted by failure of discriminant-difference additivity modulo
four.

## Decision

Do not instantiate the Ito--Takeuchi--Tsushima group law or quote its
nondegenerate commutator theorem for the current connected phase.  A future
use must first exhibit, and have the native CAS verify, one of:

1. a reduction of the complete connected sum to `xR(x)` with `R` linearized;
2. an explicit new associative cocycle on a genuinely mixed
   fibre/valuation/Witt domain, together with its commutator radical; or
3. a cohomological decomposition whose summands are the quadratic curves to
   which the cited theorem actually applies and whose signed recombination
   preserves cross-order cancellation.

The direct raw-fibre and raw-second-trace routes fail this admission test.

## Evidence

- The cited source equations are Definition 2.2 and equations (2.1)--(2.6):
  linearized `R`, the coboundary identity for `f_R`, the group law, and the
  commutator.
- ADR-0510 pins the absence of generalized-bent raw fibres.
- ADR-0523 pins the mod-four obstruction to projection-preserving extensions.
- ADR-0524 pins rank-zero and rank-two pairwise second-trace differences.

## Consequences

- The paper is a valid representation-theoretic template, but not the missing
  lemma.
- More unrestricted cocycle or rank tables are stopped unless they first
  satisfy one of the three admission conditions above.
- The active target remains the whole connected fourth cumulant, equivalently
  the aggregate Witt-Haar/conductor inequality, or a Frobenius trace
  decomposition that preserves the same signed sum.
