# ADR-0495: Exhaust the endpoint Vaughan table before aggregate regrouping

Status: accepted
Date: 2026-08-19
Index-summary: Enumerate every endpoint convolution order and Vaughan source range while keeping suppressed analytic losses explicit

## Context

ADR-0494 supplies the missing wrapped binary inverse-energy input, including
the boundary `3m=r`.  The remaining endpoint discussion still summarized
Bagshaw's Vaughan decomposition by the coarse maximum

```text
max(15N/16,2N/3+r/4).
```

That maximum locates a possible large-`d` tail, but it does not demonstrate
that every effective modulus and every Type-I or Type-II split is assigned to
a valid source case.  It also does not show directly that the problematic
Type-I Cases 4 and 5 are empty in the Lemire endpoint domain.

## Decision

Add two non-credit-bearing CAS reports to `axeyum-cas::gf2_hayes`:

- `endpoint_vaughan_range_report` exhausts one convolution order across every
  `1<=r0<=ell+1`, every Type-I split `0<=u<=floor(2r0/3)`, and every
  symmetry-reduced Type-II split
  `r0/3<v<=min(N-r0/3,N/2)`;
- `endpoint_vaughan_range_table` invokes that report for every
  `1<=d<ell` and records the first order with a strict zero-loss pointwise
  main-exponent saving.

The rows use exact numerators over denominator sixteen.  They record:

```text
small r0:       r0+N/2,
Type-I Case 1: N-r0+kappa(r0),
Type-I Case 2: min((3N+r0-u)/4,u+kappa(r0)),
Type-I Case 3: 15N/16,
Type-II Case 1: 15N/16,
Type-II Case 2: N-v/8-r0/8,
Type-II Case 3: N-r0/4.
```

An uncovered split is an error.  Empty source cases remain explicit zero-row
entries.  The reports state in their public contracts that the divisor
envelope, epsilon, constants, and convolution weights are suppressed, so a
positive main-exponent deficit is not theorem credit.

## Evidence

At `ell=300`, the complete odd and even endpoint tables each contain all
`299` convolution orders.  All seven relevant source rows occur, while
Type-I Cases 4 and 5 have zero samples because every endpoint cutoff satisfies
`N>ell+1>=r0`.

For degree 601, `d=282` has `N=320`, worst exponent `4800/16=300`, and zero
deficit.  At `d=283`, `N=319`, Type-I Case 3 is worst with exponent `4785/16`
and deficit `15/16`.  For degree 602 the corresponding first strict order is
`d=284`.  A regression constructs both complete tables, checks their order
coverage, and pins these transitions.  The focused test, all-target/all-
feature `axeyum-cas` Clippy, and workspace formatting pass.

## Alternatives

- Keep only the coarse maximum: rejected because it cannot detect an omitted
  source range or a mistaken integer endpoint.
- Treat a strict zero-loss row as endpoint closure: rejected because a
  `15/16`-bit margin cannot absorb the explicit subexponential and polynomial
  losses.
- Continue optimizing isolated cases before enumerating the source domains:
  rejected because the dominant case and residual block must be identified
  before choosing the next analytic tool.

## Consequences

- The endpoint Vaughan source-range audit is complete and replayable for both
  endpoints and every convolution order.
- The table confirms, rather than improves, the earlier `14ell/15` transition.
- The central proof blocker remains intact: preserve cancellation across the
  signed Möbius convolution, starting with a margin-aware conductor regrouping.
