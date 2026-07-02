# Model

The pack fixes one rational augmented system:

```text
A = [ 2  1 ]    b = [  5 ]
    [ 4  5 ]        [ 17 ]
```

The first pivot is `2`, and the row-two multiplier is:

```text
4 / 2 = 2
```

Applying `row_2 <- row_2 - 2 row_1` gives:

```text
[4, 5 | 17] - 2 * [2, 1 | 5] = [0, 3 | 7]
```

So the upper-triangular system is:

```text
U = [ 2  1 ]    y = [ 5 ]
    [ 0  3 ]        [ 7 ]
```

Back-substitution gives:

```text
x_2 = 7/3
x_1 = (5 - 1 * 7/3) / 2 = 4/3
```

The determinant is unchanged by the row replacement, and the product of pivots
is:

```text
2 * 3 = 6 = det(A)
```

The checked bad row isolates the final scalar contradiction:

```text
eliminated_rhs_1 = 7
eliminated_rhs_1 = 8
```
