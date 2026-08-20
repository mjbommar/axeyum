# ADR-0528: Prove the binary Hayes L-degree distribution

Status: accepted
Date: 2026-08-19
Index-summary: Replace Gao's observed binary L-degree pattern by the exact conductor count while retaining its fatal endpoint factor

## Context

Gao's improved prescribed-coefficient bound defines `D` as the sum of the
degrees of all nontrivial Hayes `L`-polynomials.  Its binary examples through
level eight exhibit

```text
d_h = 2^h,
```

where `d_h` counts the polynomials of degree `h`, and the source records the
general pattern as a conjecture.  If the aggregate degree were substantially
smaller than the coarse `(ell-1)(2^ell-1)` bound, it could conceivably improve
the endpoint ledger.

## Decision

Prove the pattern from the exact conductor filtration and expose it through
`binary_hayes_l_degree_distribution`.

A character at exact level `j` is primitive modulo `x^(j+1)`.  Since the
constant-field unit group over `GF(2)` is trivial, it is even, and its
`L`-polynomial has exact degree `j-1`.  The restriction map from the level-`j`
principal-unit character group to level `j-1` has kernel of order two.  There
are therefore exactly `2^(j-1)` characters at exact level `j`, proving

```text
d_h = 2^h  (1 <= h < ell),
D = (ell-2)2^ell+2.
```

The unique nontrivial level-one character has degree zero and does not alter
`D`.

## Evidence

- The native report constructs every count, sums the degrees with exact
  integers, and rejects unless it matches the closed form.
- A separate test enumerates the mixed-radix character group through level
  six, classifies exact conductors, and obtains the same degree populations.
- The levels five and eight reports reproduce Gao's published values `98`
  and `1538`.

## Alternatives

- Treating the finite examples as evidence for the general pattern was
  rejected; the conductor proof is exact and simpler.
- Using the exact `D` as the missing Lemire estimate was rejected.  Dividing
  by the group order leaves `D/2^ell = ell-2+2^(1-ell)`, so the characterwise
  Weil error still has a fatal linear conductor factor at the endpoint.

## Consequences

- The binary `L`-degree distribution is no longer a conjectural input in the
  Axeyum research record.
- No Lemire theorem credit moves: the open obligation remains cancellation
  inside the connected top-conductor trace, not the total degree of its
  separate character factors.
