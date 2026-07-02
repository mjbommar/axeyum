# Model

## Fixed Pivoted Factorization

The source matrix and row-swap permutation are:

```text
A = [ 1  2 ]   P = [ 0  1 ]
    [ 3  4 ]       [ 1  0 ]
```

The pivoted matrix is:

```text
P A = [ 3  4 ]
      [ 1  2 ]
```

The fixed LU factors for the pivoted matrix are:

```text
L = [ 1    0 ]   U = [ 3   4  ]
    [ 1/3  1 ]       [ 0  2/3 ]
```

and:

```text
L U = [ 3  4 ]
      [ 1  2 ] = P A
```

## Determinant Sign

The permutation swaps two rows, so:

```text
det(P) = -1
det(A) = 1*4 - 2*3 = -2
product(pivots) = 3 * (2/3) = 2
det(P) * det(A) = (-1) * (-2) = 2
```

## Triangular Solve

For `b = [3, 7]`, the row-swapped right-hand side is:

```text
P b = [7, 3]
```

Forward substitution solves `L*y = P*b`:

```text
y = [7, 2/3]
```

Back substitution solves `U*x = y`:

```text
x2 = (2/3) / (2/3) = 1
x1 = (7 - 4) / 3 = 1
x = [1, 1]
```

The validator also checks `A*x = b` exactly.

## Malformed Permutation Sign

The malformed row claims the row-swap determinant is `+1`. Exact replay
computes `-1`. The QF_LRA artifact isolates the final conflict:

```text
pivot_det = -1
pivot_det = 1
```

That is a checked finite arithmetic contradiction, not a theorem about all
pivoted-LU decompositions or about numerical pivoting algorithms.
