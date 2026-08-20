# ADR-0536: Treat the connected fibre product as a virtual trace

Status: accepted
Date: 2026-08-20
Index-summary: Expand the Hayes fourth cumulant into raw fibre products and reject an unsigned off-diagonal point-count interpretation

## Context

The Mangoldt population `N_e` is the fibre size of the characteristic-
polynomial class map from `GF(2^n)` to the truncated Hayes/Witt group.  This
makes the observed near-Gaussian fourth moment look like a fourfold
fibre-product point count.  A geometric proof must nevertheless distinguish
the positive raw collision varieties from the centred connected quantity.

## Decision

Add `ClassPopulationDistribution::connected_fibre_product_report`.  It
computes the positive raw counts

```text
C_r = sum_e N_e^r,  r=2,3,4,
```

then independently reconstructs

```text
M_2 = sum_e (N_e-mu)^2,
M_4 = sum_e (N_e-mu)^4,
K_4 = 2^ell M_4-3M_2^2.
```

The reconstruction checks every centering and pairing coefficient against the
existing direct moment and cumulant operations.  At `(ell,n)=(9,19)` the
result is

```text
K_4 = -2086965956608.
```

Thus `K_4` cannot be the cardinality of one honest off-diagonal variety.  It
is a signed virtual Frobenius trace obtained from the raw fibre products by
centering and subtraction of all three Wick pairings.

## Consequences

- Geometric irreducibility or a point-count bound for only the raw fourfold
  fibre product does not establish the connected-cumulant inequality.
- A valid geometric proof must construct and control the virtual connected
  complex, including its lower fibre products and pairing projectors, or work
  in the equivalent exact conductor-Haar representation where those
  cancellations are already explicit.
- Hast--Matei's complete-intersection viewpoint remains relevant, but its
  fixed-degree, large-field calculation and positive raw varieties do not by
  themselves give the fixed-binary growing-conductor virtual trace bound.

