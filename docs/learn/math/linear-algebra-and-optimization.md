# Linear Algebra And Optimization

Concept rows:

- `curriculum_linear_algebra`, `field_linear_algebra`, and
  `field_optimization_and_convexity` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `field_functional_analysis_and_operator_theory` in the
  [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)

Example packs:

- [linear-algebra-rational-v0](../../../artifacts/examples/math/linear-algebra-rational-v0/)
- [finite-vector-spaces-v0](../../../artifacts/examples/math/finite-vector-spaces-v0/)
- [numerical-linear-algebra-v0](../../../artifacts/examples/math/numerical-linear-algebra-v0/)
- [spectral-linear-algebra-v0](../../../artifacts/examples/math/spectral-linear-algebra-v0/)
- [matrix-invariants-v0](../../../artifacts/examples/math/matrix-invariants-v0/)
- [random-matrix-finite-v0](../../../artifacts/examples/math/random-matrix-finite-v0/)
- [finite-simplicial-homology-v0](../../../artifacts/examples/math/finite-simplicial-homology-v0/)
- [linear-optimization-v0](../../../artifacts/examples/math/linear-optimization-v0/)
- [convexity-rational-v0](../../../artifacts/examples/math/convexity-rational-v0/)
- [finite-operator-v0](../../../artifacts/examples/math/finite-operator-v0/)
- [finite-chebyshev-systems-v0](../../../artifacts/examples/math/finite-chebyshev-systems-v0/)

## What Axeyum Checks

The linear path uses exact rational matrices. It replays `A*x = b`, checks
`L*U = A`, validates a row-scaling inconsistency certificate, checks LP
feasibility witnesses, checks a tiny Farkas infeasibility certificate, and
replays finite convexity/threshold and finite-dimensional norm/operator
examples. The finite-vector-space slice adds `F2^2`, subspace/span replay,
linear-map kernel/image replay, rank-nullity by finite cardinality, and
checked non-subspace rejection. The numerical-linear-algebra
slice adds exact residual bounds, rational interval boxes for solutions, and a
one-step Jacobi contraction check. The finite random-matrix slice adds exact
matrix-valued probability tables, trace/determinant moments, expected Gram
matrices, and rank distributions. The spectral slice checks exact finite
eigenpair replay, orthogonal eigenbasis arithmetic, Rayleigh quotients, and
`P*D*P^-1` reconstruction for a fixed rational matrix. The matrix-invariants
slice checks trace, determinant, characteristic roots, Cayley-Hamilton replay,
and finite Gershgorin intervals for a fixed rational matrix. The finite
homology slice builds boundary matrices for a fixed simplicial complex,
computes exact ranks, and replays Betti numbers over `Q`. The finite
convexity slice checks midpoint Jensen replay, finite-grid second differences,
affine threshold monotonicity, and bad midpoint-convexity rejection over exact
rational data. The finite
Chebyshev-system slice checks Vandermonde unisolvence, interpolation replay,
alternating residual signs, and duplicate-node rejection over exact rational
sample grids.

This is a strong resource path because the trusted checker can be small: matrix
multiplication, vector norms, linear inequalities, and certificate arithmetic.

## Encode / Check Walkthrough

For a linear system, encode the matrix, candidate vector, and right-hand side:

```text
A = [[2, 1],
     [1,-1]]
x = [1, 2]
b = [4,-1]
```

The validator recomputes `A*x` and checks it equals `b`. For an LU witness, it
recomputes `L*U = A` and checks triangular shape. For optimization, it evaluates
each linear inequality at the candidate point and checks Farkas multipliers when
the pack claims infeasibility.

For finite-field linear algebra, encode `F2^2` as four vectors:

```text
vectors = 00, 10, 01, 11
span(10) = {00, 10}
kernel(projection_to_first_coordinate) = {00, 01}
image(projection_to_first_coordinate) = {00, 10}
```

The `finite-vector-spaces-v0` validator checks vector-space laws by
enumeration, recomputes spans, verifies linear-map preservation, and checks
rank-nullity as `dim(domain) = dim(kernel) + dim(image)`.

For convexity, the validator checks exact finite inequalities:

```text
f(x) = x^2
a = -1
b = 3
m = 1
f(m) = 1 <= (f(a) + f(b)) / 2 = 5

grid values for x^2 on -2,-1,0,1,2 = 4,1,0,1,4
second differences = 2,2,2
```

The convexity validator also rejects a false midpoint-convexity claim with
`f(-1)=0`, `f(0)=1`, and `f(1)=0`. For the numerical pack, it recomputes
`A*x_hat - b`, infinity norms, interval membership, and the first Jacobi update
using exact rational arithmetic. For random matrices, it checks finite atom
probabilities and recomputes weighted matrix statistics exactly. For spectral
linear algebra, it recomputes `A*v`, `lambda*v`, dot products, `v^T*A*v /
v^T*v`, and `P*D*P^-1` exactly. For matrix invariants, it recomputes the
characteristic polynomial, evaluates listed roots, checks `A^2 - trace(A)*A +
det(A)*I = 0`, and validates finite eigenvalue intervals.

For an operator example, the finite-operator pack checks:

```text
||A*x||_infty <= ||A||_row-sum * ||x||_infty
```

using exact rational arithmetic.

For a finite Chebyshev-system example, the validator checks the quadratic
Vandermonde matrix on sample points `-1, 0, 1`:

```text
[[1, -1, 1],
 [1,  0, 0],
 [1,  1, 1]]
```

It recomputes determinant `2`, checks interpolation values for
`2 - x + 3*x^2`, and rejects a duplicate-node grid whose determinant is `0`.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-algebra-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-vector-spaces-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/numerical-linear-algebra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/spectral-linear-algebra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/matrix-invariants-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/random-matrix-finite-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-homology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-optimization-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/convexity-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-operator-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-chebyshev-systems-v0
```

For a fuller trace through exact matrix replay and a checked LP certificate,
read [End To End: Linear System And LP Replay](linear-system-end-to-end.md).

## Horizon

General spectral theorems, rank theorems, vector-space dimension theorems,
module theory, Chebyshev-system/Haar-space theorems, minimax approximation,
conditioning, numerical stability, SDP,
general convex analysis, and algorithm convergence need proof routes or
carefully bounded numerical-experiment metadata.
