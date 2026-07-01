# Model

The pack represents an inner product on `Q^2` by a Gram matrix `G`:

```text
<u,v> = u^T G v
```

The standard row uses `G = I`. The weighted row uses:

```text
G = [[2, 1],
     [1, 2]]
```

Positive definiteness is checked by exact rational Sylvester minors in this
fixed finite-dimensional setting.

Projection onto `span(a)` is checked by:

```text
proj_a(x) = (<x,a> / <a,a>) * a
residual = x - proj_a(x)
<residual,a> = 0
```

Gram-Schmidt is checked as projection subtraction, not as a general theorem.

For the concrete projection row:

```text
target = [2,3]
basis = [1,1]
projection = [5/2,5/2]
residual = [-1/2,1/2]
<residual,basis> = 0
```

The bad projection row keeps the replayed residual but claims:

```text
<residual,basis> = 1
```

The source QF_LRA artifact reduces that malformed claim to the exact equality
conflict `residual_inner_basis = 0` and `residual_inner_basis = 1`.

## Bad Norm Certificate

For the rejected Gram matrix `diag(1,-1)` and nonzero vector `[0,1]`, exact
replay computes:

```text
norm_square = -1
```

The rejected inner-product claim requires the nonzero vector to have positive
norm square:

```text
norm_square > 0
```

The pack links that contradiction to a `QF_LRA` SMT-LIB artifact and a
resource-backed `UnsatFarkas` regression.

The general Cauchy-Schwarz, Riesz representation, projection theorem, adjoint,
spectral, and Hilbert-space completeness results remain Lean-horizon.
