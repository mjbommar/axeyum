# ADR-0510: Reject fibrewise generalized bentness and pivot to connected strata

Status: accepted
Date: 2026-08-19
Index-summary: Apply an exact modulo-eight autocorrelation criterion to every affine fibre and pivot from fibrewise Heisenberg rank to connected gcd strata

## Context

The connected Witt pushforward has full support, and ADR-0509 rejects positive
complementarity among its four primitive phases.  A remaining simple
Heisenberg route would be available if the original phase on each exact affine
Artin--Schreier fibre were generalized bent, even though many of its
coefficient ANFs are nonquadratic.

For `q:F_2^m -> Z/8`, primitive Walsh flatness is equivalent to vanishing of
every nonzero translation autocorrelation

```text
A(h)=sum_x zeta_8^(q(x+h)-q(x)).
```

If `c_r(h)` counts phase differences congruent to `r mod 8`, the minimal
polynomial `zeta_8^4+1=0` makes this an integer-only test:

```text
A(h)=0  iff  c_r(h)=c_(r+4)(h) for r=0,1,2,3.
```

## Decision

Apply this exact criterion to every recovered affine fibre before parameter or
valuation pushforward.  Record both the generalized-bent fibre count and the
number of points they contain.  Since the pinned endpoint-tail witness has no
such fibres, stop pursuing a fibre-by-fibre Gauss or Heisenberg estimate and
pivot to cancellation among connected gcd/cumulant strata.

## Evidence

At `(ell,k,d)=(9,11,8)`, all `18,884` exact affine fibres are tested and

```text
generalized-bent fibres = 0,
points in those fibres  = 0 / 130048.
```

This is stronger than the earlier ANF observation: `16,587` fibres are at
most quadratic modulo eight, yet none has a flat primitive Walsh spectrum.
The criterion accepts the known bent phase `4 x_1 x_2` on `F_2^2`; changing
its value at `(1,1)` to zero is rejected.

## Alternatives

- Applying quadratic Gauss bounds only to the at-most-quadratic fibres was
  rejected because low ANF degree does not imply a nondegenerate
  polarization, and the exact flatness test fails on every fibre.
- A larger joined group containing fibre, shift, and Witt variables is not
  logically ruled out, but no natural closed group law or associative cocycle
  has emerged.  Constructing one without a measured precursor is deferred.

## Consequences

- The simple fibrewise generalized-bent/Heisenberg route is closed for the
  pinned obstruction.
- Subsequent bounds must retain cancellation across fibres, valuations, and
  convolution orders.
- The next bounded CAS object should subtract the three Wick pairings first
  and classify the remaining connected fourth-correlation tuples by their
  polynomial gcd incidence graph.
- This is bounded negative evidence, not a proof of the endpoint estimate.
