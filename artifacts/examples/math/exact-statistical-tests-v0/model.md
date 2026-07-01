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

## Fisher Two-Sided Probability-Ordered Tail

The two-sided row uses an explicit finite convention: sum every fixed-margin
table whose point probability is no larger than the observed table's point
probability. The observed top-left count `1` has point probability `16/70`, so
counts `0`, `1`, `3`, and `4` are included:

```text
(C(4,0)*C(4,4) + C(4,1)*C(4,3) + C(4,3)*C(4,1) + C(4,4)*C(4,0)) / C(8,4)
  = (1 + 16 + 16 + 1) / 70
  = 17/35
```

The checked bad two-sided row again preserves finite replay outside the solver,
then lets QF_LRA/Farkas reject only the final rational contradiction:

```text
35 * fisher_two_sided_p_value = 17
fisher_two_sided_p_value = 1/2
```

## Exact Multinomial Probability-Ordered Tail

For the three-category multinomial row, the null probabilities are uniform and
the observed counts are `[3,0,0]`:

```text
n = 3
p = [1/3, 1/3, 1/3]
observed counts = [3,0,0]
```

The observed point probability is:

```text
3!/(3!*0!*0!) * (1/3)^3 = 1/27
```

The probability-ordered convention includes every count vector with point
probability no larger than `1/27`, namely the three all-in-one-category
vectors:

```text
[3,0,0], [0,3,0], [0,0,3]
```

So the exact multinomial p-value is:

```text
1/27 + 1/27 + 1/27 = 1/9
```

The checked bad multinomial row keeps that finite enumeration outside the
solver, then lets QF_LRA/Farkas reject only the final rational contradiction:

```text
9 * multinomial_p_value = 1
multinomial_p_value = 1/6
```

These fixed checks are finite exact replay targets. They do not claim
asymptotic test calibration or floating-point statistical-library equivalence.
