# Model

## Fixed Matrix And Vector

The source matrix is the order-4 Sylvester Hadamard matrix:

```text
H = [ 1  1  1  1
      1 -1  1 -1
      1  1 -1 -1
      1 -1 -1  1 ]
```

The source vector is:

```text
x = [1, 2, -1, 0]
```

The transform is:

```text
y = Hx = [2, -2, 4, 0]
```

The inverse reconstruction uses `H^-1 = H / 4`:

```text
H y / 4 = [1, 2, -1, 0]
```

The energy check is:

```text
||x||^2 = 1^2 + 2^2 + (-1)^2 + 0^2 = 6
||y||^2 = 2^2 + (-2)^2 + 4^2 + 0^2 = 24
24 = 4 * 6
```

## Malformed Coefficient

The second transform coefficient is:

```text
1 - 2 - 1 - 0 = -2
```

The malformed row claims the same coefficient is `-1`. The QF_LRA artifact
isolates the final conflict:

```text
transform_coefficient_1 = -2
transform_coefficient_1 = -1
```

That is a checked finite arithmetic contradiction, not a general transform
theorem.
