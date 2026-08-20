# ADR-0572: Select the one-sided relative trace target

Status: accepted
Date: 2026-08-20
Index-summary: Replace separate top-conductor maxima by the exact one-sided identity-path trace allowance left after the proved Weil prefix

## Context

ADR-0570 selected TOP-POLY, a factor-`12ell/5` improvement over individual
Weil for every parent cylinder on the top `4 ceil(log2 ell)+1` conductor
levels.  That statement is sufficient, but the paper needs only the identity
class and only a lower bound for its population.  The exact Haar identity
therefore permits two further weakenings:

1. retain cancellation between the top conductor levels; and
2. bound only the negative direction of the resulting signed trace.

Put

```text
c = ceil(log2 ell),
a = ell-c-1,
W = 2^ceil(n/2) sum_(1<=j<a) (j-1) 2^(j-1).
```

The identity-path telescope is

```text
C = sum_(a<=j<=ell) 2^(j-1) H_j(1)
  = 2^ell N_ell(1) - 2^(a-1) N_(a-1)(1).
```

The proved individual-Weil estimate bounds the omitted low part below by
`-W`.  Consequently the single strict premise

```text
(REL)  C > -(2^(2ell)-W)
```

implies `N_ell(1)>2^(n-ell)-2^ell`.

## Decision

Select REL as the paper-facing open lemma and supersede TOP-POLY as the
preferred target.  TOP-POLY remains a valid stronger sufficient statement.

Add `population_refinement_one_sided_connected_implication`.  Its typed report
retains the exact low Weil envelope, exact negative allowance, separate-level
relative Weil envelope, and integral saving still required.  It checks the
strict boundary and the allowance partition without floating point.  It does
not assert REL.

Revise `lemire-complete-proof.tex` so its sole red obligation is REL.  In the
Carlitz model, `C` is the point-count difference between conductor levels
`ell+1` and `a`; a future theorem must therefore be a one-sided relative trace
estimate, not a uniform statement about every ray class.

## Evidence

The symbolic operation checks both endpoint parities for every
`200<=ell<=1024`.  At `ell=200`, the negative allowance is just below
`(81/128) * 2^(2ell)` and the separate-level Weil envelope requires an
integral saving of 626.  The earlier symmetric quarter-target required 1,583.
At `ell=1024` the new requirement is 4,032, consistent with
`4ell+O(log ell)`.

These are arithmetic implications and exact prices, not evidence for REL.

## Consequences

- The final paper no longer asks for a maximum over all parent cylinders.
- Positive relative traces are unrestricted; only the sign that can empty the
  identity class matters.
- Cancellation across the retained Carlitz/Witt levels must be preserved.
- TOP-POLY diagnostics remain useful falsification controls but are no longer
  the load-bearing paper statement.
- Lemire's conjecture remains open until REL or a still weaker unconditional
  route is proved.
