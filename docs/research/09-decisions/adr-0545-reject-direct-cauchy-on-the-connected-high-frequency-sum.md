# ADR-0545: Reject direct Cauchy on the connected high-frequency sum

Status: accepted
Date: 2026-08-20
Index-summary: Compute the exact L2 norm after coarse-frequency and Möbius-order cancellation and show that structural-support Cauchy still loses by factors 1425 and 1483 on pinned endpoint rows

## Context

ADR-0544 expresses the connected top trace as one signed sum over only the
high additive frequencies, after every shared coarse frequency and every
Möbius order have been combined.  This is strictly more phase-preserving than
the earlier Cauchy inequality over individual top-conductor character sums.
It remained possible that a single Parseval or `L2` estimate on this final
frequency vector would meet the endpoint allowance.

## Decision

Extend `connected_top_inverse_mobius_fourier_regroup` with the exact frequency
square sum and a structural-support Cauchy ledger.  Use the proved support
bound `2^ell-2^c`, not the observed number of nonzero entries in a finite row.
Compare

```text
(2^ell-2^c) sum_alpha |F(alpha)|^2
```

with the square of the connected allowance `2^(2ell-2)` and report the exact
integral saving still required.

## Evidence

At `ell=8`, `c=3`, so the structural support has size `248`.  The pinned rows
give

```text
n=17: sum |F|^2 = 1541548032, required saving = 1425,
n=18: sum |F|^2 = 1604489216, required saving = 1483.
```

The allowance square is `268435456`, while the largest square sum compatible
with structural-support Cauchy is only `1082401`.  Both exact rows satisfy the
original signed connected trace candidate, so the loss is entirely caused by
discarding their remaining frequency phases.

Focused tests pin every integer and a public predicate rejects Cauchy credit.
The computation uses unbounded integer squares and the existing bounded exact
frequency construction.

## Consequences

- A direct positive `L2` estimate on the complete connected frequency vector
  does not explain even the pinned finite success.
- This finite obstruction does not rule out a new theorem proved only for
  `ell>=200` whose normalized square sum collapses with `ell`; such a theorem
  must state and deliver the ledgered saving explicitly.
- The selected route remains a signed high-frequency trace formula or an
  equivalent connected geometric argument.  More applications of Cauchy
  without an additional phase mechanism receive no endpoint credit.
