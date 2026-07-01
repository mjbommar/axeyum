# End To End: Rational Inner Product Spaces

This lesson follows one exact rational inner-product resource from Gram-matrix
and vector data to replayed result and proof/evidence status. It uses the
[inner-product-spaces-rational-v0](../../../artifacts/examples/math/inner-product-spaces-rational-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and `curriculum_reals`
  in the [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_linear_algebra`, `field_functional_analysis_and_operator_theory`,
  `field_numerical_analysis`, `field_optimization_and_convexity`, and
  `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `standard-inner-product-replay` | `sat` | replay-only |
| `gram-matrix-positive-definite` | `sat` | checked |
| `cauchy-schwarz-fixed-vectors` | `sat` | checked |
| `orthogonal-projection-replay` | `sat` | checked |
| `bad-projection-orthogonality-rejected` | `unsat` | checked |
| `gram-schmidt-replay` | `sat` | checked |
| `bad-inner-product-rejected` | `unsat` | checked |
| `general-inner-product-theory-lean-horizon` | `not-run` | lean-horizon |

The checked rows are exact rational finite-dimensional arithmetic rows. The
pack does not claim general Cauchy-Schwarz, projection theorem, Riesz
representation, adjoint, spectral, orthonormal-basis, or Hilbert-space
completeness theorems.

## Encode

An inner product on `Q^2` is represented by a Gram matrix:

```text
<u,v> = u^T G v
```

The standard row uses:

```text
G = [[1, 0],
     [0, 1]]
```

The fixed vectors are:

```text
u = [1, 2]
v = [3,-1]
u + v = [4, 1]
2u = [2, 4]
```

## Replay Dot Products And Bilinearity

The checker recomputes the listed dot products:

```text
<u,u> = 5
<v,v> = 10
<u,v> = 1
<u + v, u> = 6
<2u, v> = 2
```

It also checks sample bilinearity rows:

```text
<u + v, u> = <u,u> + <v,u> = 5 + 1 = 6
<2u, v> = 2*<u,v> = 2
```

These rows are exact rational arithmetic over fixed vectors.

## Replay Positive Definiteness

The weighted Gram matrix is:

```text
G = [[2, 1],
     [1, 2]]
```

The checker verifies symmetry and exact leading principal minors:

```text
minor_1 = 2
minor_2 = det(G) = 3
```

Both are positive, so this fixed `2 x 2` matrix passes the Sylvester-style
positive-definiteness check.

## Replay Cauchy-Schwarz For Fixed Vectors

For `u = [1,2]` and `v = [3,-1]`, the checker computes:

```text
<u,v>^2 = 1
<u,u>*<v,v> = 5 * 10 = 50
```

The fixed Cauchy-Schwarz inequality is therefore:

```text
1 <= 50
```

This is not a proof of the general theorem; it is the exact replay of one
finite-dimensional instance.

## Replay Orthogonal Projection

The projection row projects:

```text
target = [2, 3]
basis  = [1, 1]
```

The coefficient is:

```text
<target,basis> / <basis,basis> = 5 / 2
```

So the projection and residual are:

```text
projection = [5/2, 5/2]
residual   = [-1/2, 1/2]
```

The checker verifies orthogonality and the norm split:

```text
<residual,basis> = 0
||target||^2 = 13
||projection||^2 = 25/2
||residual||^2 = 1/2
13 = 25/2 + 1/2
```

The bad projection row keeps the same replayed residual but claims:

```text
<residual,basis> = 1
```

After exact replay computes `<residual,basis> = 0`, the source `QF_LRA`
artifact exposes the final equality conflict. The route regression requires an
`Evidence::UnsatFarkas` certificate and independently checks it.

## Replay Gram-Schmidt

The input basis is:

```text
[1, 1], [1, 0]
```

The listed orthogonal basis is:

```text
[1, 1], [1/2, -1/2]
```

The checker recomputes the second projection and residual:

```text
projection coefficient = 1/2
second projection = [1/2, 1/2]
second residual = [1/2, -1/2]
```

Then it checks:

```text
<[1,1], [1/2,-1/2]> = 0
det(input basis) = -1
det(orthogonal basis) = -1
```

So the vectors are orthogonal and both lists remain bases.

## Check The Refutation

The bad row claims this Gram matrix defines a real inner product:

```text
G = [[1,  0],
     [0, -1]]
```

The checker evaluates the norm square of `[0,1]`:

```text
<[0,1], [0,1]> = -1
```

An inner product must have positive norm square for every nonzero vector. The
pack exposes the refutation as a `QF_LRA` contradiction:

```text
norm_square = -1
norm_square > 0
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check. The determinant is also negative:

```text
det(G) = -1
```

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/inner-product-spaces-rational-v0
cargo test -p axeyum-solver --test math_resource_lra_routes inner_product_bad_projection_orthogonality_artifact_emits_checked_farkas
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for exact finite-dimensional
analysis:

```text
untrusted fast search -> Gram matrix, vectors, projection, orthogonal basis
trusted small checking -> rational arithmetic, positivity, orthogonality
proof upgrade -> QF_LRA/Farkas certificate for negative norm and projection conflicts
```

General Cauchy-Schwarz, Gram-Schmidt over arbitrary spaces, Hilbert projection,
Riesz representation, adjoints, spectral theorems, and Hilbert-space
completeness require Lean/mathlib-scale proof support.
