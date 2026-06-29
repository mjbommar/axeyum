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

## `qf-lia-bad-binomial-tail-count`

Expected result: `unsat`.

The SMT-LIB artifact encodes the rejected binomial p-value numerator as an
integer count contradiction: `C(4,3) = 4`, `C(4,4) = 1`, `tail_count = 4 + 1`,
and the false claim `tail_count = 4`. Axeyum emits and checks an
`UnsatDiophantine` certificate for those inconsistent equalities.
