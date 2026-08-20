# ADR-0543: Retain convolution-order cancellation in the connected top projector

Status: accepted
Date: 2026-08-20
Index-summary: Decompose the connected top-conductor trace exactly by Möbius order and reject any proof strategy that bounds those surviving orders separately

## Context

The endpoint reduction selects the signed top-conductor trace

```text
2^ell Delta_(ell,n)-2^(a-1) Delta_(a-1,n),
```

where `a=ell-ceil(log2(ell))-1`.  Separately, the exact identity-class
Möbius convolution expresses each discrepancy as a signed sum over interval
degrees.  It was possible that taking the fine-minus-coarse projector would
remove the low convolution orders and leave only a structurally easier tail.

## Decision

Add `connected_top_mobius_convolution`.  Apply the fine and coarse scales to
each convolution order before taking an absolute value, require the uniform
main terms to cancel, and check that the signed order sum reconstructs the
selected top-conductor trace exactly.  Expose the first nonzero order and the
number of nonzero orders so that a claimed support cutoff is replayable.

## Evidence

For `ell=8`, the exact connected order vectors at the two endpoint degrees
are

```text
n=17: [-768, 8192, -2304, 2048, 10240, 15360, -21504]
n=18: [-4096, 7168, 9984, 0, -5120, 13824, -3584].
```

They sum to `11264` and `18176`, respectively, matching the independently
selected traces.  Order one survives at both endpoints.  Every order survives
at the odd endpoint, while six of seven survive at the even endpoint.  The
ordinary test pins every entry and declines when the coarse quotient is not
positive.

## Consequences

- The top-conductor projector does not create a minimum Möbius order or a
  high-order-only support theorem.
- Bounding the connected contributions order by order discards cancellation
  that is already present in both endpoint rows.
- A valid endpoint argument must retain the complete signed sum across
  convolution orders, for example through the existing frequencywise
  annihilator-depth regrouping or a stronger two-parameter trace formula.
- This is an exact bounded diagnostic, not an asymptotic cancellation theorem
  and not proof credit for the Lemire endpoint.
