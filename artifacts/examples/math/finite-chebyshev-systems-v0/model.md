# Model

## Vandermonde Unisolvence

The finite unisolvence witness uses sample points:

```text
x = -1, 0, 1
basis = 1, x, x^2
```

The evaluation matrix is:

```text
[[1, -1, 1],
 [1,  0, 0],
 [1,  1, 1]]
```

The checker recomputes determinant `2`, so this finite grid has no nonzero
quadratic coefficient vector vanishing at all three sample points.

## Interpolation

For coefficients:

```text
p(x) = 2 - x + 3*x^2
```

the checker recomputes:

```text
p(-1) = 6
p(0) = 2
p(1) = 4
```

## Alternating Residual

The alternation witness uses:

```text
r(x) = x^2 - 1/2
```

at `-1, 0, 1`, giving residual values:

```text
1/2, -1/2, 1/2
```

The checker verifies nonzero alternating signs and common magnitude `1/2`.

## Bad Grid

The bad-grid row uses duplicate sample points `0, 0, 1`. The checker recomputes
determinant `0` and verifies that the nonzero polynomial `x - x^2` vanishes on
all listed sample points.

## Axeyum Route

The finite replay computes the degenerate determinant and null vector. The
solver-facing artifact then checks the final exact-rational conflict:

```text
determinant = 0
determinant = 1
```

This is a QF_LRA/Farkas row. It does not prove general Chebyshev-system or
minimax theorems; those remain Lean-horizon claims.
