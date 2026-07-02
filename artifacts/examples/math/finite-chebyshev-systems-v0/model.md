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

The bad interpolation-sample row keeps the same coefficients but claims
`p(1) = 5`. The pack validator checks the coefficient sum
`2 + (-1) + 3 = 4`; the separate solver-facing QF_LRA row then rejects the
false sample value `5` with checked Farkas evidence.

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

The bad alternating-residual row keeps this same table but claims uniform error
`2/3`. The validator recomputes the residual values, signs, and common
magnitude, then the separate solver-facing QF_LRA row rejects:

```text
uniform_error = 1/2
uniform_error = 2/3
```

## Bad Grid

The bad-grid row uses duplicate sample points `0, 0, 1`. The checker recomputes
determinant `0` and verifies that the nonzero polynomial `x - x^2` vanishes on
all listed sample points.

## Axeyum Route

The finite replay computes the degenerate determinant, null vector,
interpolation value, and alternation magnitude. The solver-facing artifacts
are separate checked rows that then check small exact-rational conflicts such as:

```text
determinant = 0
determinant = 1
uniform_error = 1/2
uniform_error = 2/3
```

These are QF_LRA/Farkas rows. They do not prove general Chebyshev-system or
minimax theorems; those remain Lean-horizon claims.
