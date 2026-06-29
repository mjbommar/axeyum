# Checks

## `mean-variance-identity`

Expected result: `sat`.

The validator recomputes mean, second moment, and population variance for the
finite sample `[1, 2, 3, 4]` exactly.

## `contingency-table-margins`

Expected result: `sat`.

The validator recomputes row sums, column sums, and total count for the fixed
`2x2` contingency table.

## `simpson-paradox-witness`

Expected result: `sat`.

The validator checks the exact rate inequalities: treatment `A` is better than
`B` in both strata, but `B` is better after aggregating the strata. This is a
finite count-table witness, not a causal conclusion.
