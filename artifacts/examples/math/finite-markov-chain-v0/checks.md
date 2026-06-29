# Checks

## `stochastic-matrix-witness`

Expected result: `sat`.

The validator checks every transition entry is in `[0, 1]` and each row of the
three-state transition matrix sums exactly to `1`.

## `finite-horizon-distribution-replay`

Expected result: `sat`.

The validator starts from `[1, 0, 0]`, applies the transition matrix twice, and
checks the listed one-step distribution, two-step distribution, and
fixed-horizon absorption probability.

## `stationary-distribution-witness`

Expected result: `sat`.

The validator checks that `[1/3, 2/3]` is normalized and satisfies
`pi * P = pi` exactly.

## `bad-stochastic-row-rejected`

Expected result: `unsat`.

The second row of the malformed transition matrix sums to `2/3`, so the matrix
cannot be row-stochastic. This is a checked finite arithmetic rejection, not an
emitted proof object yet.
