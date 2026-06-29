# Checks

## `mean-variance-identity`

Expected result: `sat`.

The validator recomputes mean, second moment, and population variance for the
finite sample `[1, 2, 3, 4]` exactly.

Proof route: finite-model replay today. A future impossible rational statistic
claim should emit a QF_LRA/Farkas certificate instead of relying on this SAT
witness row.

## `contingency-table-margins`

Expected result: `sat`.

The validator recomputes row sums, column sums, and total count for the fixed
`2x2` contingency table.

Proof route: finite-model replay today. A future inconsistent integer margin
claim should emit a QF_LIA/Diophantine certificate.

## `simpson-paradox-witness`

Expected result: `sat`.

The validator checks the exact rate inequalities: treatment `A` is better than
`B` in both strata, but `B` is better after aggregating the strata. This is a
finite count-table witness, not a causal conclusion.

Proof route: finite-model replay today. General causal claims stay outside
proof status; impossible rational-rate or integer-count constraints should use
the LRA/LIA certificate routes named in the pack metadata.
