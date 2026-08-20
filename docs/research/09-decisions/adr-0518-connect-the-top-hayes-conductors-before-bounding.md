# ADR-0518: Connect the top Hayes conductors before bounding

Status: accepted
Date: 2026-08-19
Index-summary: Replace separate top-level square-root assumptions by one signed relative ray-class trace with an explicit quarter-scale endpoint budget

## Context

ADR-0517 reduces the endpoint population to binary Haar increments `H_j(b)`.
The first hybrid ledger then uses the proved individual Weil estimate below
`ell-ceil(log2 ell)` and a conjectural square-root-fibre estimate at each
remaining level.  That implication is valid, but it still takes an absolute
value between conductor levels.  The preceding Witt experiments show that
cross-layer cancellation is essential, and Lemire needs only the identity
class rather than a uniform bound over every parent cylinder.

Along the identity path, the weighted increments telescope exactly:

```text
sum_(j=a)^ell 2^(j-1) H_j(1)
  = 2^ell N_ell(1) - 2^(a-1) N_(a-1)(1).             (CT)
```

The same quantity is the sum of the degree-`n` Mangoldt transforms over all
characters whose conductor level is at least `a`.  It is therefore one
relative ray-class/Witt trace, not a collection of unrelated estimates.

## Decision

Put

```text
L = ceil(log2 ell)+1,
a = ell-L.
```

Retain every level `a<=j<=ell` inside (CT), and use the proved individual Weil
bound only for `j<a`.  Isolate the single analytic target

```text
abs(2^ell N_ell(1) - 2^(a-1) N_(a-1)(1)) <= 2^(2ell-2).  (CRT)
```

Add `population_refinement_connected_top_implication` for the symbolic
endpoint ledger.  Extend the exact finite refinement report with the identity
path, the signed connected top trace, and an independent telescoping check
from the fine and coarse populations.

For both endpoint degrees, the proved low-conductor contribution is less than
`2^(2ell-1)` for every `ell>=200`: its normalized value is at most

```text
(ell-L-3)/2^L + 2^(2-ell) < 1/2.
```

Assumption (CRT) contributes one quarter of the target.  Hence their sum is
strictly below `2^(2ell)`, proving the earlier `2^ell` population-discrepancy
bound with reserve.  At `ell=200`, (CT) contains only the ten levels
`191<=j<=200`.

The CAS also reports the sum of the individual Weil envelopes on the same
window and the smallest integral factor required to reduce it to (CRT).  At
both `ell=200` endpoints the exact ratio is `50641/32`, hence the required
integer saving is `1583`; uniformly it is asymptotic to `8ell`.  This is the
stopping test for a proposed connected geometric argument.

## Evidence boundary

The exact level-12 odd and even connected traces are respectively `1,400,832`
and `1,339,392`, both below the candidate `4,194,304`.  The CAS also checks the
symbolic implication through a broad integer range.  Both endpoint traces pass
for every fleet-tested `16<=ell<=20`; at `ell=20` their absolute
candidate-normalized ratios are approximately `0.0087` and `0.0227`.  These
are diagnostics and arithmetic implications, not a proof of (CRT).

## Consequences

- The open statement is one identity-class relative trace, allowing
  cancellation across all top conductor levels.
- Compared with the summed individual Weil envelope, (CRT) asks for only a
  polynomial conductor saving, rather than the exponential per-level gain in
  the stronger square-root-fibre conjecture.
- A characteristic-two Witt/Heisenberg or relative Artin--Schreier argument
  should target (CT) directly.  Proving separate valuation or conductor bounds
  and summing absolute values is no longer the selected route.
- The stronger square-root-fibre fact remains a valid sufficient alternative,
  but it is not the minimal paper lemma.
