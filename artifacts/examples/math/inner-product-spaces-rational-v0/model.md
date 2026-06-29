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
The general Cauchy-Schwarz, Riesz representation, projection theorem, adjoint,
spectral, and Hilbert-space completeness results remain Lean-horizon.
