# Model

The model is a fixed finite binary-classification training table.

## Classes

```text
positive -> 1
negative -> 0
```

## Features

```text
color in {red, blue}
shape in {square, circle}
```

## Gini Impurity

For a node with `p` positive rows and `n` negative rows:

```text
total = p + n
Gini(p, n) = 1 - (p / total)^2 - (n / total)^2
           = 2*p*n / total^2
```

For a split with children `c`, weighted impurity is:

```text
sum_c (count(c) / total) * Gini(c)
```

The checked finite object is exact rational arithmetic over the committed
counts. No floating-point tolerance is used.

## Fixed Table

The eight-row table has four positive and four negative rows. The root Gini
impurity is therefore:

```text
Gini(4, 4) = 2*4*4 / 8^2 = 1/2
```

The candidate `color` split has child counts `(3,1)` and `(1,3)`:

```text
Gini(3, 1) = 3/8
Gini(1, 3) = 3/8
weighted_color = (4/8)*(3/8) + (4/8)*(3/8) = 3/8
gain_color = 1/2 - 3/8 = 1/8
```

The candidate `shape` split has child counts `(2,2)` and `(2,2)`:

```text
Gini(2, 2) = 1/2
Gini(2, 2) = 1/2
weighted_shape = 1/2
gain_shape = 0
```

The best split among the committed candidates is `color`.
