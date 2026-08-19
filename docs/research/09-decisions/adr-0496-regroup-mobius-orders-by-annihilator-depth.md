# ADR-0496: Regroup Möbius orders by annihilator depth, not conductor alone

Status: accepted
Date: 2026-08-19
Index-summary: Preserve cross-order cancellation by low-bit Fourier annihilator depth and charge a buffered tail against the exact odd-endpoint margin

## Context

The pointwise Vaughan table in ADR-0495 covers every source range but cannot
close the endpoint after its suppressed losses are restored.  A proposed next
step was to regroup frequencies "by conductor" because a frequency belongs to
`W_d^perp` while its first `d` bits vanish.

Those are different filtrations.  Membership in `W_d^perp` is controlled by
the number of vanishing low packed Fourier bits.  The multiplicative exact-
conductor filtration already used by the Hayes character tools is not enough
to recover that value, so grouping by conductor alone would lose the nesting
that permits cancellation across `d`.

## Decision

Call the relevant quantity the **annihilator depth** `v(a)` and add
`inverse_mobius_fourier_regroup`.  It checks the exact identity

```text
2^ell Delta_(ell,n)
  = sum_a sum_(1<=d<=v(a),d<ell) d 2^d H_(n-d)(a).
```

The operation constructs every exact `H_(n-d)`, checks each order against the
existing Möbius-convolution term, combines all eligible orders at each
frequency, and groups the result by `v(a)`.  It returns cellwise, orderwise,
and layerwise absolute numerators, but grants no uniform cancellation credit.

Also add `odd_endpoint_vaughan_tail_budget`.  It restores `ceil(log2 d)`, adds
a caller-visible analytic-loss reserve over denominator sixteen, rounds each
tail order upward, and subtracts the resulting absolute tail bound from the
exact sufficient odd-endpoint budget `2^(ell+1)-2`.

## Evidence

For both endpoints and every `2<=ell<=8`, the regrouped numerator equals
`2^ell Delta` exactly.  Each annihilator layer has its forced population:
`2^(ell-v-1)` for `v<ell` and one zero frequency at `v=ell`.  The raw
cellwise absolute numerator dominates both regrouped absolute ledgers, as
required by the triangle inequality.

At `ell=300`, even with zero analytic reserve, charging the tail from `d=292`
costs `2^301`, exceeding the odd positivity budget by two.  Starting at
`d=293` costs `2^300` and leaves residual low/medium-block budget
`2^301-2^300-2`.  This proves that the first zero-loss pointwise saving at
`d=283` is not a usable tail boundary after the factor `d` and summation are
restored.

Finally, inserting `H_k=B_k-B_(k-1)` gives the exact fixed-depth summation-by-
parts identity

```text
sum_(d=1)^v d 2^d H_(n-d)
  = 2B_(n-1)+sum_(d=2)^v (d+1)2^(d-1)B_(n-d)
    -v2^v B_(n-v-1).
```

It isolates a boundary term and a weighted `B` combination; it supplies no
bound for either.

## Alternatives

- Group by the existing multiplicative exact conductor only: rejected because
  it does not determine membership in `W_d^perp`.
- Take absolute values before summing over `d`: rejected because it discards
  the cancellation this increment is intended to preserve.
- Call the zero-reserve pointwise transition a buffered tail: rejected because
  restoring only `d` and summation moves the first usable `ell=300` boundary
  from `283` to `293`.

## Consequences

- The CAS now represents the exact aggregate structure needed by the next
  proof attempt, rather than only independent convolution orders.
- ADR-0497 now charges the exact finite inverse-energy divisor envelope in a
  parallel tail column.  The remaining reserve is only for analytic
  Vaughan-weight loss and constants, and the `ell=300` explicit-energy tail
  does not fit.
- The remaining theorem obligation is a bound for the annihilator-depth-
  aggregated weighted `B` combination on the low/medium block.  Multiplicative
  conductor or Berlekamp rank may refine that two-parameter problem, but cannot
  replace the annihilator-depth index.
