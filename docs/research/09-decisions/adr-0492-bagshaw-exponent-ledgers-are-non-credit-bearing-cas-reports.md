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

Add four exact arithmetic diagnostics to `axeyum-cas::gf2_hayes`:

- `binary_type_one_case_one_exponent` checks the exact Case-1 integer range
  and the replacement `N-r0/2 -> N-r0+kappa(r0)`;
- `binary_type_one_case_two_exponent` maximizes
  `min((3N+r0-u)/4,u+kappa(r0))` over every integer `u` in the exact Case-2
  range, including both endpoints and the two integers around the crossing;
- `binary_type_one_case_five_exponent` computes the worst Case-5 exponent
  `2n/3+kappa(r0)/2` over denominator six and compares it with the trivial
  exponent `n`;
- `endpoint_inverse_mobius_exponent_calibration` computes the zero-epsilon
  calibration `max(15N/16,2N/3+r/4)` over denominator 48 for one endpoint
  convolution order, where `N=k+1` is forced by the exact
  `H_k=C_(k+1)-2C_k+C_(k-1)` bridge.

All four reports use checked integer arithmetic.  Their names, documentation,
and fields state that they are diagnostics, not theorem certificates.  They
grant no proof credit and do not expose SMT predicates.

## Evidence

At `n=r0=300`, the binary Case-5 ledger is exactly trivial:

```text
kappa=200,  2n/3+kappa/2=300.
```

At `(n,r0)=(300,320)` its exponent is `306.5`, exceeding trivial by `6.5`.
Residue-class rounding can yield a constant one-sixth saving, but not a
uniform power saving.

The two previously prose-only Type-I cases retain genuine binary savings.  In
Case 1 the exact admissible interval is

```text
0 <= u <= min(floor(2r0/3),N-r0),
```

and the replacement bound is independent of `u`:

```text
N-r0+kappa(r0) = N-ceil((r0-1)/3).
```

Thus it saves exactly `ceil((r0-1)/3)` from the trivial exponent `N`.  At
`(N,r0)=(601,301)` the report gives exponent `501`, a saving of `100`, over
the full interval `0<=u<=200`.

In Case 2 the exact integer interval is

```text
max(0,N-r0) <= u
             <= min(floor(r0/3),N-ceil(r0/3)).
```

The energy line `A(u)=(3N+r0-u)/4` decreases and the completion line
`B(u)=u+kappa(r0)` increases.  Therefore the worst combined bound occurs at
an interval endpoint or one of the two integers surrounding
`u=(3N+r0-4kappa(r0))/5`.  The implementation checks precisely those
candidates in constant time; a separate unit-test oracle enumerates every
admissible `u` for all `1<=r0<=40` and `1<=N<=2r0`.  For
`(N,r0)=(300,300)` the crossing is `u=80` and the bound is `280`, saving `20`.
For `(350,300)` the crossing lies beyond the interval, so the exact optimizer
selects the upper endpoint `u=100` and obtains exponent `300`, saving `50`.
ADR-0494 now supplies the previously open internal wrapped binary energy input
behind `A(u)`, including `u=r0/3`.  The Case-2 report nevertheless records
that its displayed quarter-exponent suppresses the explicit divisor envelope
and any epsilon/constants reserve; these zero-loss savings remain calibration,
not endpoint proof credit.

This is a boundary on a full binary port, not a Lemire endpoint blocker.
Bagshaw's Case 5 assumes `n<=r0`, whereas every Lemire cumulative cutoff in
the endpoint calibration satisfies `N>ell+1>=r0`.  That report exposes this
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
- The claim that Cases 1 and 2 retain a binary saving is now backed by exact,
  replayable range and optimization ledgers rather than prose substitution.
- The large-`d` tail that a future binary inverse-Möbius theorem could cover is
  distinguished from the linear-sized uncovered range.
- The Lemire-specific analytic obligation is the linear-sized low/medium-`d`
  block.  It must preserve cancellation across `d` or use the
  Berlekamp/Artin--Schreier structure; Case 5 is not added to that obligation.
