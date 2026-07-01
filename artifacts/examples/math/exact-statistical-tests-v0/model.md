# Model

All probabilities are exact rationals written as strings accepted by Python's
`Fraction` type. Counts are finite nonnegative integers.

## Binomial Tail

For `n = 4`, `k = 3`, and null probability `p0 = 1/2`, the right-tail p-value
is:

```text
P(X >= 3) = C(4,3)*(1/2)^3*(1/2)^1 + C(4,4)*(1/2)^4 = 5/16
```

## Hypergeometric Point Probability

For the fixed table

```text
[[1, 3],
 [3, 1]]
```

with row sums `[4,4]` and column sums `[4,4]`, the probability of top-left
count `1` under fixed margins is:

```text
C(4,1)*C(4,3) / C(8,4) = 8/35
```

## Fisher Left Tail

The one-sided left-tail p-value for the same table sums possible top-left
counts `0` and `1` under the same fixed margins:

```text
(C(4,0)*C(4,4) + C(4,1)*C(4,3)) / C(8,4) = 17/70
```

The checked bad Fisher row preserves that finite replay boundary, then lets
QF_LRA/Farkas reject only the final rational contradiction:

```text
70 * fisher_left_tail_p_value = 17
fisher_left_tail_p_value = 1/4
```

These fixed checks are finite exact replay targets. They do not claim
asymptotic test calibration or floating-point statistical-library equivalence.
