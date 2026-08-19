# ADR-0517: Expose the raw-population Haar triangle

Status: accepted
Date: 2026-08-19
Index-summary: Reconstruct every endpoint population from binary Witt sibling imbalances and isolate a sufficient square-root-fibre envelope that closes both endpoint ledgers

## Context

ADR-0515 targets the aggregate connected fourth cumulant, and ADR-0516 rejects
the naive growing-block Fomenko quotient.  The same quotient filtration admits
a first-moment identity that had not been exposed.  Let `N_j(b)` be the sum of
the full level-`ell` Mangoldt populations below a class `b` of `E_j`.  If the
two children of a parent cylinder have populations `N_j(b,0)` and
`N_j(b,1)`, put

```text
H_j(b)=N_j(b,0)-N_j(b,1).
```

Every leaf population can be reconstructed from the root total and these
signed sibling differences.  This gives a direct sufficient endpoint theorem
before squaring any imbalance or taking a fourth moment.

## Decision

Add `ClassPopulationDistribution::population_refinement_triangle`.  It
aggregates every quotient level, pairs its binary fibres, records
`H_j^*=max_b |H_j(b)|`, and checks leaf by leaf that

```text
2^ell N_ell(e)
 = 2^degree + sum_(j=1)^ell sign_j(e) 2^(j-1) H_j(parent_j(e)).
```

Consequently

```text
T(ell,n)=sum_(j=1)^ell 2^(j-1) H_j^* <= 2^(2ell)
```

implies `max_e |N_ell(e)-2^(n-ell)|<=2^ell`.  The public report checks this
finite implication and refuses malformed/nonbinary quotients or excessive
projection work.

Retain the buffered analytic target

```text
H_j^* <= 3j 2^ceil((n-j)/2).                       (RF)
```

The separate symbolic operation substitutes (RF) into the exact triangle. It
closes the odd endpoint for every `ell>=13` and the even endpoint for every
`ell>=15`.  This is an implication checker, not a proof of (RF).

## Evidence

The ordinary mutation-resistant test reconstructs both level-12 endpoints and
pins the non-tautological level-4 odd failure `272>256`.  Exact fleet runs at
both endpoints for every `16<=ell<=20` satisfy the raw triangle.  At level 20,
the observed numerator/target ratios are approximately `0.0583` and `0.0880`.

The initially proposed coefficient two in (RF) is false.  At
`(ell,n,j)=(19,40,4)`, the exact maximum is `2,112,512`, while
`2j 2^ceil((n-j)/2)=2,097,152`.  The coefficient-three target retains a real
buffer and still closes long before the existing degree-400 finite handoff.

These computations are finite diagnostics.  They establish the Haar identity
and the arithmetic implication, not the uniform square-root-fibre estimate.

## Consequences

- The endpoint can be finished by a family of conditional one-bit refinement
  estimates without proving the fourth-cumulant bound.
- The required scale is square root in the residual fibre dimension, with
  only a linear conductor factor.  This is a precise target for relative
  Artin--Schreier--Witt or long-cycle geometry.
- Unlike the failed per-valuation claim, `H_j` already aggregates the complete
  Mangoldt population at one conductor level; no valuation layer is bounded
  separately.
- The connected-cumulant route remains active in parallel.  Neither route has
  theorem credit until its uniform analytic estimate is proved.
