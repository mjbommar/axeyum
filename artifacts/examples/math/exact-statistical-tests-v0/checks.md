# Checks

## `binomial-tail-pvalue`

Expected result: `sat`.

The validator recomputes the exact finite binomial right-tail sum for
`n = 4`, `k = 3`, and `p0 = 1/2`.

## `hypergeometric-point-probability`

Expected result: `sat`.

The validator recomputes the fixed-margin hypergeometric point probability for
the listed `2x2` table.

## `fisher-left-tail-pvalue`

Expected result: `sat`.

The validator sums the exact fixed-margin hypergeometric probabilities for all
top-left counts at or below the observed top-left count.

## `bad-binomial-pvalue-rejected`

Expected result: `unsat`.

The exact right-tail p-value is `5/16`, so the claimed value `1/4` is false.
This is a checked finite arithmetic rejection, not an emitted proof object yet.
