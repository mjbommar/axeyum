# ADR-0544: Cancel coarse additive frequencies before Möbius bounds

Status: accepted
Date: 2026-08-20
Index-summary: Embed the coarse quotient spectrum into the fine additive Fourier domain and cancel it exactly before grouping the surviving top frequencies by Möbius order or annihilator depth

## Context

ADR-0543 shows that the connected top-conductor projector does not remove low
Möbius convolution orders.  The earlier additive Fourier regroup preserves
signed cancellation across those orders, but it had been applied separately
at the fine and coarse conductor levels.  Taking an absolute value between
those levels would discard the cancellation selected by the connected trace.

## Decision

Add `connected_top_inverse_mobius_fourier_regroup`.  Compute the fine and
coarse inverse-additive Walsh spectra, require every coarse spectrum to equal
the low-frequency slice of the corresponding fine spectrum, inflate the
coarse convolution into the fine frequency domain, and subtract it before any
absolute value.

For coarse level `c=a-1`, quotient compatibility of unit inversion gives

```text
H_k^(ell)(alpha)=H_k^(c)(alpha),  0<=alpha<2^c.
```

For nonzero `alpha` in this range, its low-bit annihilator depth is below `c`,
so the eligible convolution orders at the two levels are identical.  At
`alpha=0`, every relevant `H_k(0)` is the total degree-`k` polynomial Möbius
sum and vanishes because `k>=2`.  Hence every inflated coarse frequency
cancels exactly, leaving

```text
CT = sum_(2^c <= alpha < 2^ell)
       sum_(1<=d<=v(alpha)) d 2^d H_(n-d)^(ell)(alpha),
```

where `v(alpha)` is its number of vanishing low bits.

## Evidence

The native operation checks quotient compatibility degree by degree, requires
the first `2^c` connected frequency numerators to be zero, and independently
reconstructs the trace from both the Möbius-order decomposition and the fine
minus coarse populations.  Ordinary tests cover both endpoint parities for
`6<=ell<=8` and pin the complete `ell=8` annihilator-layer vectors.

At `ell=8`, the raw cellwise, connected-order, frequencywise, and final
annihilator-layer absolute totals are respectively

```text
n=17: 313952, 60416, 162672, 71280,
n=18: 415264, 43776, 205856, 70208.
```

The two middle totals are not ordered, confirming that Möbius order and
annihilator depth are cross-cutting regroupings rather than a nested sequence
of triangle inequalities.

## Consequences

- The connected trace has an exact high-additive-frequency support theorem;
  no coarse character need be estimated.
- The surviving support still has size `2^ell-2^c`, so this identity alone is
  not the required endpoint cancellation bound.
- A valid analytic lemma should act on the complete displayed signed sum.  It
  must not bound conductors, Möbius orders, or annihilator layers separately
  unless its ledger absorbs the corresponding measured loss.
- The operation is a replayable exact representation and grants no universal
  Lemire theorem credit.
