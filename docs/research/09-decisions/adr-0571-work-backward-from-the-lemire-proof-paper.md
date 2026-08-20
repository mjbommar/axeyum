# ADR-0571: Work backward from the Lemire proof manuscript

Status: accepted
Date: 2026-08-20
Index-summary: Freeze the sub-five-page proof surface and require every new Lemire estimate to discharge its sole open top-conductor lemma

## Context

The lane has accumulated several sufficient reductions, exact diagnostics, and
refuted candidate mechanisms.  ADR-0570 selected the weakest current endpoint
obligation,

```text
(TOP-POLY)  (12 ell H_j^*)^2 <= 25 (j-1)^2 2^n
```

on the moving window
`ell-4ceil(log2 ell)<=j<=ell`, for the two endpoint degrees.  Continuing to
develop estimates without placing them in the final proof risks proving a
stronger statement than the application consumes or losing a required
proper-power margin.

The source-level Hast--Matei audit also confirms that their fourth-moment
theorem is not an almost-complete citation at `q=2`.  It fixes `m,n,h`, lets
`q` grow, permits its constant to depend on `n,h`, and assumes `p>n` when
`m>2`.  Both the wild singular-locus replacement and a small degree-uniform
constant would be new theorems.  ADR-0567 already records this exact boundary.

## Decision

Add `docs/research/10-cas/lemire-complete-proof.tex` as the paper-facing proof
surface.  It is deliberately under five pages in its compact build and has a
fail-visible red notice while `(TOP-POLY)` remains open.  It contains:

1. the reciprocal identity-ray-class reduction;
2. the exact binary Haar reconstruction;
3. the individual Hayes/RH bound;
4. `(TOP-POLY)` as the sole open mathematical lemma;
5. the parity-safe geometric closing calculation;
6. the odd identity and even proper-power subtraction; and
7. the independently checked degree-400 handoff.

New analytic or algebraic work receives endpoint credit only after it is
substituted into this proof surface and discharges `(TOP-POLY)` or replaces it
with a strictly weaker fully proved route.  Finite recurrence rows remain
falsification controls and cannot remove the red notice.

## Consequences

- The requested final artifact now exists in its intended compact form, but
  it is explicitly not share-ready and makes no unconditional theorem claim.
- The proof frontier is visible in the manuscript rather than recoverable only
  from the research ledger.
- A repaired Hast--Matei tameness argument with an uncontrolled
  degree-dependent constant does not count as progress toward the paper.
- The next CAS theorem should target the near-diagonal sibling difference
  directly; another unrestricted spectrum table is out of scope.
