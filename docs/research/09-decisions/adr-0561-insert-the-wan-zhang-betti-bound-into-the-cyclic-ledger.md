# ADR-0561: Insert the Wan--Zhang Betti bound into the cyclic ledger

Status: accepted
Date: 2026-08-20
Index-summary: Apply the sharper complete-intersection Betti theorem to Sawin's ordered-root variety and quantify why it still misses the binary endpoint

## Context

ADR-0550 compresses the von Mangoldt long-cycle character into cyclic Foulkes
summands with coefficient mass `2^omega(n)`.  Its endpoint ledger previously
compared the required cyclic-eigenspace multiplicity only with Sawin's generic
bound `3(n+2)^(n+ell)`.  Wan and Zhang's 2026 complete-intersection theorem is
a newer positive result that explicitly sharpens this input in Sawin's
short-interval application.

For a complete intersection in `A^n` cut out by `r` equations of degree at
most `d`, their theorem gives

```text
B_c <= binom(n-1,r-1)(d+1)^n.
```

Sawin's ordered-root variety is cut out by the first `ell` elementary
symmetric polynomials, so `r=d=ell` is a valid uniform specialization.

## Decision

Extend `SawinFoulkesEndpointLedger` with the exact Wan--Zhang value

```text
B_WZ(n,ell)=binom(n-1,ell-1)(ell+1)^n,
```

its squared Foulkes cost, and the strict endpoint verdict after Sawin's weight
and the proved proper-prime-power envelope are restored.  Compute the binomial
coefficient with exact `BigUint` arithmetic; do not replace it by the looser
`(2ell+2)^n` display when evaluating the endpoint.

The theorem materially improves the old generic bound, but it does not close
Lemire.  At the degree-400 handoff the exact sizes are

```text
n     bit length of B_WZ   bit length of squared error   margin bits
401          3464                    7231                    402
402          3473                    7255                    404
```

Thus the new theorem still misses by 6,829 and 6,851 bits respectively.  The
reason is structural: Wan--Zhang bounds the total cohomology of the complete
intersection, while the Foulkes reduction needs a polynomial-size effective
long-cycle eigenspace or its signed Frobenius trace.  A sharper generic total
Betti estimate cannot by itself provide that representation-specific
cancellation.

## Evidence

Focused tests pin the exact degree-12 specialization
`binom(11,4)6^12`, require the new bound to improve Sawin's previous generic
bound at degrees 401 and 402, and require both exact endpoint comparisons to
remain false.  The existing Foulkes tests independently retain Ramanujan
orthogonality, coefficient mass, Sawin weight, and proper-power strictness.

## Consequences

- The most recent general complete-intersection technology is now represented
  in the executable exponent ledger rather than omitted from the literature
  comparison.
- The positive theorem improves constants but does not move the proof
  frontier: the remaining target is still a cyclic-eigenspace bound such as
  `B(n,r)<=n^4`, or a direct Frobenius--long-cycle trace estimate.
- No Lemire fact changes status and no finite or conditional result receives
  universal theorem credit.

## Reference

- D. Wan and D. Zhang, [*Betti number bounds for varieties and exponential
  sums*](https://arxiv.org/abs/2501.12623), especially the affine
  complete-intersection theorem and its explicit discussion of Sawin's
  short-interval varieties.
