# ADR-0589: Spend translation zeros before pricing WITT-LOW

Status: accepted
Date: 2026-08-21
Index-summary: Remove every proved translation zero from the endpoint Weil ledger and retain the unchanged factor-626 odd price

## Context

ADR-0588 determines exactly which primitive Hayes characters translation
forces to have zero Mangoldt spectrum.  The selected one-sided endpoint ledger
still prices its low and top conductor blocks using the full exact-character
population `2^(j-1)`.  Before asking a new theorem for `(WITT-LOW)`, every
proved zero must be removed from that envelope.

## Decision

Add `translation_adjusted_one_sided_connected_implication` as a separate
report.  At exact level `j`, replace the individual Weil term

```text
2^(j-1) (j-1) 2^ceil(n/2)
```

by

```text
(2^(j-1)-z_(j,n)) (j-1) 2^ceil(n/2),
```

where ADR-0588 proves

```text
z_(j,n)=0                                      if n or j is even,
z_(1,n)=1                                     if n is odd,
z_(j,n)=2^((j-3)/2)                           if n and j>=3 are odd.
```

The report performs this subtraction separately below and inside the connected
top window.  The improved low envelope enlarges the permitted harmful-negative
trace, while the improved top envelope lowers the trace that the missing
theorem must control.  Both improvements are retained as exact integers beside
the baseline; the existing manuscript ledger is not silently changed.

## Evidence

At the first odd endpoint `(ell,n)=(200,401)`, the top window is
`191<=j<=200`.  Translation removes exactly

```text
2^94                                      low-window characters,
31 * 2^94                                top-window characters.
```

Both adjusted envelopes improve strictly, but their ratio still has integer
ceiling `626`.  At `(200,402)`, every forced-zero count is zero and the ledger
is identical to the baseline.  The focused regression checks these integers
and verifies for both endpoint parities through `ell=1024` that adjustment can
never increase the requested saving.

## Consequences

- The translation theorem has now been completely spent in the selected
  endpoint argument; no proved translation zero remains available to credit a
  later step.
- At the first unresolved odd endpoint, the residual signed trace still needs
  a factor-626 improvement over the adjusted separate-Weil envelope.  The even
  endpoint receives no improvement at all.
- `(WITT-LOW)`, `(REL)`, and Lemire's conjecture remain open.  The next theorem
  must cancel residual nonfixed characters or the connected trace across
  conductors; recounting translation-fixed characters cannot close it.
