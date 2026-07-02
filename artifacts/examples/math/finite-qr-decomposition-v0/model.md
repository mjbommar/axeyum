# Model

## Fixed Matrices

The source matrices are:

```text
Q = [  3/5  4/5 ]
    [ -4/5  3/5 ]

R = [ 5  1 ]
    [ 0  2 ]
```

The columns of `Q` are orthonormal:

```text
(3/5)^2 + (-4/5)^2 = 1
(4/5)^2 + (3/5)^2 = 1
(3/5)(4/5) + (-4/5)(3/5) = 0
```

`R` is upper triangular because its lower-left entry is `0`.

The product is:

```text
A = Q R = [  3  11/5 ]
          [ -4   2/5 ]
```

## Malformed Product Entry

The bottom-right product entry is:

```text
(-4/5) * 1 + (3/5) * 2 = 2/5
```

The malformed row claims the same entry is `1/2`. The QF_LRA artifact isolates
the final conflict:

```text
qr_product_11 = 2/5
qr_product_11 = 1/2
```

That is a checked finite arithmetic contradiction, not a theorem about all QR
decompositions or about numerical QR algorithms.
