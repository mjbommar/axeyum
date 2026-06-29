# Checks

## `sign-diagonal-moments`

Expected result: `sat`.

The validator normalizes the diagonal-sign matrix distribution and recomputes
the exact trace, trace-square, determinant, and invertibility moments.

## `expected-gram-matrix`

Expected result: `sat`.

For each listed atom, the validator computes `A^T A`; then it checks the exact
weighted average against the listed identity matrix.

## `rank-mixture-probabilities`

Expected result: `sat`.

The validator computes exact matrix rank by rational row reduction, groups atom
probabilities by rank, and checks the listed rank probabilities and expected
rank.

## `bad-trace-moment-rejected`

Expected result: `unsat`.

The diagonal-sign distribution has exact `E[tr(A)^2] = 2`, so the claimed value
`1` is false. This is a checked finite arithmetic rejection, not an emitted
proof object yet.
