# Model

The model is a fixed finite binary-classification training table restricted to
dyadic node proportions.

## Classes

```text
positive -> 1
negative -> 0
```

## Features

```text
color in {red, green, blue}
shape in {square, circle}
```

## Dyadic Entropy

For a node with `p` positive rows and `n` negative rows and `total = p + n`,
the binary entropy in bits is:

```text
H(p, n) = -(p/total)*log2(p/total) - (n/total)*log2(n/total)
```

with the convention `0 * log2(0) = 0`. This pack only commits nodes whose
class proportion `p/total` lies in `{0, 1/2, 1}`:

```text
H(pure node)     = 0        (log2(1) = 0)
H(balanced node) = 1        (log2(1/2) = -1)
```

so every entropy value is an exact rational and no logarithm approximation
enters the replay. A node with any other proportion would make `log2`
irrational; the validator rejects such tables, and the general case stays on
the Lean horizon.

For a split with children `c`, the weighted entropy and information gain are:

```text
weighted = sum_c (count(c) / total) * H(c)
gain     = H(root) - weighted
```

The checked finite object is exact rational arithmetic over the committed
counts. No floating-point tolerance is used.

## Fixed Table

The eight-row table has four positive and four negative rows. The root
entropy is therefore:

```text
H(4, 4) = 1
```

The candidate `color` split has child counts `(2,0)`, `(0,2)`, and `(2,2)`:

```text
H(2, 0) = 0
H(0, 2) = 0
H(2, 2) = 1
weighted_color = (2/8)*0 + (2/8)*0 + (4/8)*1 = 1/2
gain_color = 1 - 1/2 = 1/2
```

The candidate `shape` split has child counts `(2,2)` and `(2,2)`:

```text
H(2, 2) = 1
H(2, 2) = 1
weighted_shape = 1
gain_shape = 0
```

The best split among the committed candidates is `color`.
