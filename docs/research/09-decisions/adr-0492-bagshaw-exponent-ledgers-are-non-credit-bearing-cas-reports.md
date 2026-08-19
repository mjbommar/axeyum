# ADR-0492: Keep Bagshaw exponent ledgers as non-credit-bearing CAS reports

Status: accepted
Date: 2026-08-19
Index-summary: Check the binary Type-I obstruction and endpoint interval cutoffs exactly without treating odd-characteristic exponents as a GF(2) theorem

## Context

The exact Fourier bridge reduces the Lemire endpoint discrepancy to
Möbius-weighted inverse-additive sums.  Bagshaw's 2024 paper gives closely
matching bounds, but globally assumes odd characteristic.  Its Type-I proof
uses a square-root complete Kloosterman estimate that is unavailable for the
binary prime-power modulus.  Axeyum instead proves the weaker uniform exponent

```text
kappa(r)=r-ceil((r-1)/3).
```

Substituting exponents informally is error-prone: one internal Vaughan range
loses all power saving, while a direct endpoint use of the published exponent
pair covers only the largest interval degrees.

## Decision

Add two exact arithmetic diagnostics to `axeyum-cas::gf2_hayes`:

- `binary_type_one_case_five_exponent` computes the worst Case-5 exponent
  `2n/3+kappa(r0)/2` over denominator six and compares it with the trivial
  exponent `n`;
- `endpoint_inverse_mobius_exponent_calibration` computes the zero-epsilon
  calibration `max(15N/16,2N/3+r/4)` over denominator 48 for one endpoint
  convolution order, where `N=k+1` is forced by the exact
  `H_k=C_(k+1)-2C_k+C_(k-1)` bridge.

Both reports use checked integer arithmetic.  Their names, documentation, and
fields state that they are diagnostics, not theorem certificates.  They grant
no proof credit and do not expose SMT predicates.

## Evidence

At `n=r0=300`, the binary Case-5 ledger is exactly trivial:

```text
kappa=200,  2n/3+kappa/2=300.
```

At `(n,r0)=(300,320)` its exponent is `306.5`, exceeding trivial by `6.5`.
Residue-class rounding can yield a constant one-sixth saving, but not a
uniform power saving.

This is a boundary on a full binary port, not a Lemire endpoint blocker.
Bagshaw's Case 5 assumes `n<=r0`, whereas every Lemire cumulative cutoff in
the second report satisfies `N>ell+1>=r0`.  The endpoint report exposes this
domain separation explicitly.

For `ell=300`, the zero-epsilon endpoint calibration first lies strictly below
`2^ell` at `d=283` for degree 601 and at `d=284` for degree 602.  At the prior
odd boundary, `N=320` and `15N/16=300` exactly, so strict closure fails.  Unit
tests pin these transitions and reject invalid parameter domains.

## Alternatives

- Cite Bagshaw's final theorem at `q=2`: rejected because the paper fixes odd
  `q` and the complete-sum dependency is genuinely characteristic-sensitive.
- Replace the square-root exponent and retain the published final exponent:
  rejected because the checked Case-5 arithmetic reaches or exceeds the
  trivial bound.
- Record only a prose calculation: rejected because endpoint shifts by one and
  the common-denominator inequalities are exactly the sort of bookkeeping the
  CAS should replay.

## Consequences

- The failed full-range port is localized to a precise Vaughan range, and
  that range is explicitly marked empty for the Lemire endpoint cutoffs.
- The large-`d` tail that a future binary inverse-Möbius theorem could cover is
  distinguished from the linear-sized uncovered range.
- The Lemire-specific analytic obligation is the linear-sized low/medium-`d`
  block.  It must preserve cancellation across `d` or use the
  Berlekamp/Artin--Schreier structure; Case 5 is not added to that obligation.
