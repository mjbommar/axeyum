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
cannot be row-stochastic.

The resource-backed Axeyum regression checks the final linear obligation as
`QF_LRA`: `p10 = 1/3`, `p11 = 1/3`, `row_sum = p10 + p11`, and
`row_sum = 1`, requiring rechecked `UnsatFarkas` evidence.

## `bad-stationary-distribution-rejected`

Expected result: `unsat`.

The claimed distribution `[1/2, 1/2]` is normalized but not stationary for the
two-state chain. Exact replay computes:

```text
[1/2, 1/2] * P = [3/8, 5/8]
```

The resource-backed Axeyum regression checks the first-coordinate contradiction
as `QF_LRA`: `8 * pi_next_a = 3` and `pi_next_a = 1/2`, requiring rechecked
`UnsatFarkas` evidence.
