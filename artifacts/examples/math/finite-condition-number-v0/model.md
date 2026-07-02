# Model

The source matrix is diagonal:

```text
A = [[2, 0],
     [0, 1/3]]
```

The listed inverse is:

```text
A^-1 = [[1/2, 0],
        [0, 3]]
```

Exact matrix multiplication gives:

```text
A * A^-1 = I
A^-1 * A = I
```

Using the matrix infinity norm, the maximum absolute row sum:

```text
||A||_infinity = max(2, 1/3) = 2
||A^-1||_infinity = max(1/2, 3) = 3
kappa_infinity(A) = 2 * 3 = 6
```

The perturbation row uses:

```text
x = [1, 1]
b = A*x = [2, 1/3]
delta_b = [0, 1/30]
delta_x = A^-1*delta_b = [0, 1/10]
```

The perturbed solve is consistent:

```text
b + delta_b = [2, 11/30]
x + delta_x = [1, 11/10]
A * (x + delta_x) = b + delta_b
```

The relative perturbation and response are:

```text
||b||_infinity = 2
||delta_b||_infinity = 1/30
relative_b = 1/60

||x||_infinity = 1
||delta_x||_infinity = 1/10
relative_x = 1/10
```

The condition-number shadow checks:

```text
relative_x <= kappa_infinity(A) * relative_b
1/10 <= 6 * 1/60
```

This finite model keeps exact rational conditioning separate from
floating-point stability.
