# ADR-0497: Use the exact binary divisor envelope in Vaughan ledgers

Status: accepted
Date: 2026-08-19
Index-summary: Replace the crude subexponential divisor factor by an exact finite-degree optimizer and carry it through every endpoint energy row

## Context

ADR-0494 proved a wrapped inverse-additive-energy bound over
`GF(2)[x]/(x^r)`, but its finite factorization count used a deliberately crude
low/high-degree divisor envelope.  ADR-0495 then replayed Bagshaw's endpoint
Vaughan cases using the ideal asymptotic energy exponents.  The two reports
were not connected end to end: the range table could say where a zero-loss
main exponent saved while the proved finite envelope could consume that
margin.

For a nonzero binary polynomial

```text
Q = product_P P^(e_P),
```

the number of ordered monic factorizations `Q=RS` is exactly
`tau(Q)=product_P(e_P+1)`.  The exact number `I_j` of available irreducibles
of degree `j` satisfies

```text
2^j = sum_(d|j) d I_d.
```

This permits an exact finite optimization instead of a generic divisor bound.

## Decision

Compute the maximum of `tau(Q)` for `deg Q<=D` by dynamic programming.  For
each irreducible degree `j`, fix a total exponent `E` and a number `t<=I_j` of
used irreducibles.  The product is maximal when the positive exponents are as
balanced as possible.  A degree knapsack then combines the independent
`j`-blocks.  Cache the resulting prefix maxima because every energy stratum
uses the same theorem at a different `D`.

Retain both exponent columns in the endpoint Vaughan report:

- the published ideal energy exponent, for source comparison; and
- the ceiling obtained from Axeyum's explicit wrapped energy bound with the
  exact finite divisor maximum inserted.

Propagate both columns into the odd-tail margin report.  The caller reserve is
now only for the remaining analytic/Vaughan-weight loss and constants; it is
not allowed to stand in for the energy divisor factor.

## Evidence

Direct Berlekamp factorization of every monic binary polynomial through degree
ten gives the same prefix maximum as the dynamic program.  The existing exact
inverse-energy tables remain below the sharpened wrapped envelope.

At `ell=300`, the ideal table first saves at `d=283`, but no convolution order
has a strict explicit-energy pointwise bound.  Even the last odd order
`d=299` has exponent `4906/16`, against target `4800/16`; its worst row is the
balanced Type-II case at effective modulus `152` and split `151`.  Therefore
the formerly advertised zero-reserve tail from `d=293` is explicitly
optimistic: it fits only in the ideal column, not after the proved finite
energy envelope is charged.

A non-credit diagnostic at the last odd order shows the explicit column is
below target by `12/16` at `ell=1000`.  This is evidence of the
expected sublinear divisor loss, not an endpoint theorem or a monotonicity
proof.

## Alternatives

- Keep the low/high-degree divisor envelope: rejected because it loses about
  one hundred bits after the endpoint Hölder substitution at `ell=300`.
- Continue to expose only a caller reserve: rejected because it permits an
  ideal exponent to masquerade as the proved finite bound.
- Drop the ideal column: rejected because it remains useful for auditing the
  source proof and locating the analytic transition independently of finite
  constants.

## Consequences

- The inverse-energy theorem now has a much sharper explicit finite constant,
  independently checked at small degrees.
- Every energy-using Type-I/Type-II row exposes the actual proved ceiling.
- Pointwise Vaughan still does not prove the endpoint.  The low/medium signed
  aggregate remains the central obstruction, and the exact finite envelope
  shows that a rigorous tail also needs a larger asymptotic buffer than the
  ideal ledger suggested.
