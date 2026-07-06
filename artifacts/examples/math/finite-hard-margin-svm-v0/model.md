# Model

The model is a fixed finite hard-margin support-vector-machine primal-dual
pair over rational data.

## Classes And Labels

```text
positive -> label +1
negative -> label -1
```

## Hard-Margin Program

The hard-margin SVM for a separable training set is the quadratic program

```text
minimize   (1/2) * ||w||^2
subject to y_i * (w . x_i + b) >= 1   for every training point
```

Its KKT system uses one nonnegative multiplier `alpha_i` per constraint:

```text
stationarity:             w = sum_i alpha_i * y_i * x_i
multiplier/label balance: sum_i alpha_i * y_i = 0
complementary slackness:  alpha_i * (y_i * (w . x_i + b) - 1) = 0
```

Every quantity in this pack is rational, so the whole primal-dual pair
replays with exact arithmetic. No floating-point tolerance is used.

## Fixed Data

Training points:

```text
s1 = (2, 2),   y = +1   (support vector)
s2 = (0, 0),   y = -1   (support vector)
p2 = (3, 3),   y = +1
p3 = (1, 4),   y = +1
n2 = (-1, -1), y = -1
n3 = (0, -2),  y = -1
```

Committed hyperplane and multipliers:

```text
w     = (1/2, 1/2)
b     = -1
alpha = 1/4 on s1 and s2, and 0 elsewhere
```

## Margins, KKT, And Duality Gap

Functional margins `y * (w . x + b)` at the committed hyperplane:

```text
s1: +1 * (2 - 1)         = 1     (on the margin)
s2: -1 * (0 - 1)         = 1     (on the margin)
p2: +1 * (3 - 1)         = 2
p3: +1 * (5/2 - 1)       = 3/2
n2: -1 * (-1 - 1)        = 2
n3: -1 * (-1 - 1)        = 2
```

All constraints hold with minimum margin `1`, and only the two support
vectors sit exactly on the margin.

KKT identities:

```text
stationarity: 1/4*(2, 2) - 1/4*(0, 0) = (1/2, 1/2) = w
balance:      1/4 - 1/4 = 0
slackness:    alpha_i * (margin_i - 1) = 0 for every point
```

Objectives:

```text
||w||^2 = 1/2
primal  = (1/2) * ||w||^2                          = 1/4
dual    = sum(alpha) - (1/2) * ||sum(alpha*y*x)||^2 = 1/2 - 1/4 = 1/4
gap     = 0
```

The zero gap is replayed as committed exact-rational data. The strong-duality
and KKT-sufficiency theorems that turn a zero gap into an optimality proof
stay in the horizon row. The geometric margin `1/||w|| = sqrt(2)` divides by
an irrational norm and stays outside this pack.
