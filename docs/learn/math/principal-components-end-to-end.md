# Exact Finite Principal Component Checks

This page follows
[finite-principal-components-v0](../../../artifacts/examples/math/finite-principal-components-v0/).
It shows how Axeyum treats a PCA-style computation as exact finite rational
replay, not as a theorem about arbitrary PCA or a floating-point algorithm.

## The Finite Object

The pack fixes four observations:

```text
(-2,  0)
( 2,  0)
( 0, -1)
( 0,  1)
```

The exact mean is `(0, 0)`, so centering leaves the rows unchanged. The centered
Gram and covariance matrices are:

```text
X^T X =
  [ 8  0 ]
  [ 0  2 ]

C = (1/4) X^T X =
  [ 2    0 ]
  [ 0  1/2 ]
```

The total variance is `trace(C) = 5/2`.

## The Principal Component

The principal component is the first coordinate direction:

```text
v1 = (1, 0)
lambda1 = 2
C v1 = (2, 0)
```

The secondary direction is:

```text
v2 = (0, 1)
lambda2 = 1/2
C v2 = (0, 1/2)
```

Projection onto `v1` gives scores:

```text
[-2, 2, 0, 0]
```

The one-component reconstruction drops the second coordinate. The residual
energy is `2`, the total centered energy is `10`, and the explained-variance
ratio is:

```text
2 / (5/2) = 4/5
```

## The Bad Claim

The malformed row claims the principal eigenvalue is `3/2`. The source
SMT-LIB artifact isolates the final contradiction:

```text
vx = 1
2 * vx = lambda
lambda = 3/2
```

The QF_LRA route emits `UnsatFarkas` evidence and independently rechecks it.

## Trust Boundary

```text
finite replay        -> recompute mean, covariance, eigenpairs, scores, residuals
checked evidence     -> reject the malformed principal-eigenvalue equality
theorem horizon      -> PCA/SVD optimality, statistics, perturbation, floating point
```

This is Axeyum's core pattern in a statistics/numerical-linear-algebra setting:
untrusted search may propose a component or a corrupted scalar, but trusted
small checking recomputes the exact finite claim being displayed.

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-principal-components-v0

cargo test -p axeyum-solver --test math_resource_lra_routes finite_principal_components_bad_eigenvalue_artifact_emits_checked_farkas

python3 scripts/query-foundational-resources.py checks --pack finite-principal-components-v0 --route Farkas --proof-status checked --require-any
```

The first command checks the finite model, the second command checks the Farkas
evidence route, and the third command verifies that consumers can find the
promoted checked row through the public JSON/query boundary.
