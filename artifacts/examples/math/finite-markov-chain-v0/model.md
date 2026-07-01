# Model

All transition probabilities and distribution entries are exact rationals
written as strings accepted by Python's `Fraction` type. A Markov transition
matrix is row-major:

```text
P[i][j] = probability of moving from state i to state j
```

The checker requires a square matrix with nonnegative entries and every row sum
equal to `1`.

## Finite-Horizon Evolution

For the three-state absorbing chain:

```text
P = [[1/2, 1/2, 0],
     [0,   1/2, 1/2],
     [0,   0,   1]]
```

starting from `[1, 0, 0]`, the validator recomputes:

```text
v1 = [1/2, 1/2, 0]
v2 = [1/4, 1/2, 1/4]
```

The fixed-horizon absorption probability after two steps is therefore `1/4`.

## Stationary Distribution

For

```text
P = [[1/2, 1/2],
     [1/4, 3/4]]
```

the validator checks:

```text
[1/3, 2/3] * P = [1/3, 2/3]
```

These are finite exact replay targets. They do not prove general convergence,
mixing time, or infinite-state stochastic-process theorems.

## Bad Stochastic Row

The negative row fixes a two-state matrix whose second row is malformed:

```text
P(1,0) = 1/3
P(1,1) = 1/3
row_sum = P(1,0) + P(1,1)
row_sum = 1
```

Exact replay computes `row_sum = 2/3`; the final contradiction is linear over
exact rationals and is checked by an `UnsatFarkas` regression.

## Bad Stationary Distribution

The stationary-distribution negative row reuses the valid two-state transition
matrix but proposes the wrong distribution:

```text
pi = [1/2, 1/2]
```

Exact replay computes:

```text
pi * P = [3/8, 5/8]
```

The first coordinate must equal `1/2` if the distribution is stationary, but
the replayed value is `3/8`; the final contradiction is linear over exact
rationals and is checked by an `UnsatFarkas` regression.
