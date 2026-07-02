# Matrix Computation Index

This index groups the current matrix-flavored math resources by the kind of
claim Axeyum can check today. It is a navigation page, not a new proof route:
each row points back to a validated pack, a focused lesson, and the existing
checker or certificate path.

For the promotion boundary between educational examples, solver regressions,
and benchmark-corpus claims, see
[Matrix Corpus And Benchmark Boundary](matrix-corpus-benchmark-boundary.md).
For downstream discovery by computation family plus proof route, see
[Matrix Computation Consumer Queries](../../foundational-resources/MATRIX-COMPUTATION-QUERIES.md).
For the focused finite-operator and Chebyshev slice, see
[Chebyshev And Operator Replay Index](chebyshev-operator-index.md).
For finite matrix-valued probability tables and moment replay, see
[Random Matrix Moment Index](random-matrix-moment-index.md).
For finite sample covariance replay, see
[End To End: Finite Covariance Matrix](covariance-matrix-end-to-end.md).
For exact Hessian solves inside Newton steps, see
[End To End: Finite Newton Step](newton-step-end-to-end.md).
For exact rational condition numbers and perturbation-bound shadows, see
[End To End: Finite Condition Number](condition-number-end-to-end.md).
For exact Schur complements, determinant/inverse block shadows, and
conditional-variance shadows, see
[End To End: Finite Schur Complement](schur-complement-end-to-end.md).
For exact Gaussian-elimination row-operation transcripts, see
[End To End: Finite Gaussian Elimination](gaussian-elimination-end-to-end.md).
For exact singular-value, spectral-norm, and SVD reconstruction shadows, see
[End To End: Finite Singular-Value Shadow](singular-value-shadow-end-to-end.md).
For exact Jordan-chain and generalized-eigenvector shadows, see
[End To End: Finite Jordan Chain](jordan-chain-end-to-end.md).
For finite vector-space, dual-space, module, and tensor rows as theorem
shadows, see
[Linear Algebra Structure Theorem Boundary](linear-algebra-structure-theorem-boundary.md).

Concept rows:

- `bridge_lu_replay`, `bridge_schur_complement`, `bridge_rank_nullity`, `bridge_residual_bound`,
  `bridge_eigenpair`, `bridge_characteristic_polynomial`,
  `bridge_random_matrix_finite_moment`,
  `bridge_finite_boundary_operator_replay`,
  `bridge_finite_torsion_homology_replay`,
  `bridge_finite_cohomology_replay`,
  `bridge_finite_universal_coefficient_shadow`,
  `bridge_finite_cup_product_replay`,
  `bridge_inner_product_projection`, `bridge_module_action`,
  `bridge_tensor_bilinearity`, and
  `bridge_finite_operator_chebyshev` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `field_linear_algebra`, `field_numerical_analysis`,
  `field_optimization_and_convexity`, `field_probability_theory`,
  `field_statistics`, `field_abstract_algebra`, and
  `field_functional_analysis_and_operator_theory` in the
  [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)

## Route Map

| Theme | Packs | What Is Checked | Route |
|---|---|---|---|
| Linear systems, Gaussian elimination, nullspaces, LU, QR, and Cholesky | [linear-algebra-rational-v0](../../../artifacts/examples/math/linear-algebra-rational-v0/), [finite-gaussian-elimination-v0](../../../artifacts/examples/math/finite-gaussian-elimination-v0/), [finite-qr-decomposition-v0](../../../artifacts/examples/math/finite-qr-decomposition-v0/), [finite-cholesky-decomposition-v0](../../../artifacts/examples/math/finite-cholesky-decomposition-v0/), [linear-optimization-v0](../../../artifacts/examples/math/linear-optimization-v0/) | Fixed `A*x = b`, one exact elimination row operation, pivot multiplier and pivot product replay, back-substitution, `L*U = A`, `Q^T Q = I`, `Q*R = A`, `L*L^T = A`, positive leading minors, exact bad elimination/LU/QR/Cholesky replay, separate checked bad scalar or product-entry proof rows, bad nullspace component rejection, singular-row inconsistency, LP objective thresholds | finite replay plus QF_LRA/Farkas |
| Block matrices and Schur complements | [finite-schur-complement-v0](../../../artifacts/examples/math/finite-schur-complement-v0/) | Exact leading-block inverse, one-by-one Schur complement, determinant factorization, two-sided inverse replay, positive-definite shadow, conditional-variance shadow, replay-only bad scalar rejection, and separate checked bad scalar proof row | finite replay plus QF_LRA/Farkas |
| Residuals, Hessian solves, condition numbers, singular values, and numerical shadows | [numerical-linear-algebra-v0](../../../artifacts/examples/math/numerical-linear-algebra-v0/), [finite-condition-number-v0](../../../artifacts/examples/math/finite-condition-number-v0/), [finite-singular-value-shadow-v0](../../../artifacts/examples/math/finite-singular-value-shadow-v0/), [finite-newton-step-v0](../../../artifacts/examples/math/finite-newton-step-v0/), [least-squares-regression-v0](../../../artifacts/examples/math/least-squares-regression-v0/) | Exact residual norms, solution boxes, one Jacobi step, infinity-norm condition number, singular-value/SVD shadow replay, spectral and Frobenius norms, perturbation-bound replay, Hessian linear solve, Newton direction, normal equations, residual orthogonality, RSS improvement, bad condition-number bound, bad singular-value bound, bad Newton coordinate, and bad RSS rejection | finite replay plus QF_LRA/Farkas |
| Inner products, projections, and orthogonal transforms | [inner-product-spaces-rational-v0](../../../artifacts/examples/math/inner-product-spaces-rational-v0/), [finite-walsh-hadamard-transform-v0](../../../artifacts/examples/math/finite-walsh-hadamard-transform-v0/) | Gram matrices, fixed Cauchy-Schwarz, orthogonal projection, Gram-Schmidt, order-4 Walsh-Hadamard transform replay, inverse reconstruction, Parseval energy scaling, bad negative norm, bad projection orthogonality, and bad transform coefficient | finite replay plus QF_LRA/Farkas |
| Kernel, image, rank, and duals | [finite-vector-spaces-v0](../../../artifacts/examples/math/finite-vector-spaces-v0/), [finite-dual-spaces-v0](../../../artifacts/examples/math/finite-dual-spaces-v0/) | Finite `F2` vector-space tables, subspaces, linear maps, kernel/image, rank-nullity, covectors, annihilators, transpose maps | finite table replay plus QF_UF/Alethe |
| Modules and tensors | [finite-modules-v0](../../../artifacts/examples/math/finite-modules-v0/), [finite-tensor-products-v0](../../../artifacts/examples/math/finite-tensor-products-v0/) | Scalar actions, generated submodules, module homomorphisms, quotients, bilinear maps, tensor basis rows, Kronecker products | finite table replay plus QF_UF/Alethe |
| Spectral, singular-value, and Jordan-chain rows | [spectral-linear-algebra-v0](../../../artifacts/examples/math/spectral-linear-algebra-v0/), [finite-singular-value-shadow-v0](../../../artifacts/examples/math/finite-singular-value-shadow-v0/), [finite-jordan-chain-v0](../../../artifacts/examples/math/finite-jordan-chain-v0/), [matrix-invariants-v0](../../../artifacts/examples/math/matrix-invariants-v0/) | Eigenpairs, orthogonal eigenbasis arithmetic, Rayleigh quotients, bad Rayleigh quotients, spectral reconstruction, `A^T A` singular-vector equations, SVD reconstruction, generalized-eigenvector chains, nilpotent-part replay, Jordan reconstruction, trace, determinant, characteristic roots, Cayley-Hamilton, Gershgorin intervals, bad singular-value bounds, bad Jordan components, bad trace, and bad characteristic-polynomial rows | finite replay plus QF_LRA/Farkas |
| Random matrices and covariance | [random-matrix-finite-v0](../../../artifacts/examples/math/random-matrix-finite-v0/), [finite-covariance-matrix-v0](../../../artifacts/examples/math/finite-covariance-matrix-v0/) | Finite matrix-valued probability tables, trace/determinant moments, expected Gram matrices, rank mixture probabilities, sample means, centered Gram matrices, covariance matrices, positive-semidefinite shadows, bad trace-square, bad expected-rank, and bad covariance-entry rows | finite expectation/rank/covariance replay plus QF_LRA/Farkas |
| Chain, cochain, cup-product, and torsion matrices | [finite-simplicial-homology-v0](../../../artifacts/examples/math/finite-simplicial-homology-v0/), [finite-chain-complex-torsion-v0](../../../artifacts/examples/math/finite-chain-complex-torsion-v0/), [finite-simplicial-cohomology-v0](../../../artifacts/examples/math/finite-simplicial-cohomology-v0/), [finite-universal-coefficient-shadow-v0](../../../artifacts/examples/math/finite-universal-coefficient-shadow-v0/), [finite-simplicial-cup-products-v0](../../../artifacts/examples/math/finite-simplicial-cup-products-v0/) | Boundary matrices, boundary squared, Betti-rank replay, boundary-square coefficient cancellation, one-entry Smith diagonal replay, `Z/2` torsion quotient, integer dual cochain maps, finite Hom/Ext shadow bookkeeping, F2 coboundary matrices, cohomology-rank replay, finite F2 cup-product table replay, bad oriented-boundary coefficient, bad boundary-square coefficient, bad torsion generator, bad `H^1 = 0`, bad coboundary value, bad cup-product value | finite replay plus QF_LIA/Diophantine, QF_UF/Alethe, or QF_BV/DRAT |
| Operators and interpolation matrices | [finite-operator-v0](../../../artifacts/examples/math/finite-operator-v0/), [finite-chebyshev-systems-v0](../../../artifacts/examples/math/finite-chebyshev-systems-v0/) | Operator norm bounds, matrix action, Chebyshev recurrence, bad Chebyshev-prefix value, Vandermonde unisolvence, interpolation values, alternating residuals | finite replay plus QF_LRA/Farkas |

## What The Checker Trusts

For exact rational rows, the trusted work is small arithmetic: matrix-vector
row operations, matrix-vector multiplication, matrix multiplication,
Schur-complement scalar replay,
determinant or trace formulas for the
fixed dimension, exact residuals, rational inequalities, and Farkas certificate
checking when a row is unsatisfiable. The linear-system slice now has one
Gaussian-elimination transcript with a checked bad eliminated-RHS row, and the
LU slice has a positive `L*U = A` replay row, a bad product-entry replay row,
an explicit checked bad product-entry proof row, and a checked nullspace
component row, so
consumers can see the replay/certificate boundary without leaving the core
matrix pack.

For finite algebraic rows, the trusted work is table replay: enumerate the
finite carrier, recompute addition, scalar action, function evaluation,
kernel/image membership, and the one bad equality or closure condition. The
QF_UF/Alethe route checks the equality-heavy contradiction after replay exposes
it.

For chain and cochain rows, the trusted work is exact finite matrix arithmetic:
integer boundary matrices for homology, the one-entry Smith diagonal `[2]` for
the torsion quotient, integer transpose/cochain replay for the finite
universal-coefficient shadow, and F2 coboundary matrices for cohomology, plus
ordered-simplex F2 cup-product table replay and small checked contradiction
rows when a malformed value or group identity is claimed. This is useful for finite
algebraic-topology examples, but it is not a proof of homology invariance,
general Smith normal form, universal coefficient theorems, cohomology-ring
laws, or cohomology-operation invariance.

## What Remains A Horizon

The finite rows do not prove general rank-nullity, Schur-complement theorem,
block inverse theorem, Gaussian-elimination correctness, spectral theorem,
Jordan normal form, diagonalizability criteria, Cayley-Hamilton over arbitrary
rings, Hilbert projection, Riesz representation,
Hahn-Banach, stability or conditioning of numerical algorithms, asymptotic
random-matrix laws, covariance-estimator consistency, PCA theorem claims,
minimax approximation, general Smith normal form,
classification of finitely generated abelian groups, homology invariance,
universal coefficient theorems, exact sequences, Ext/Tor laws, cohomology
operation laws, cohomology-ring quotienting, or cohomology invariance. Those
claims remain Lean-horizon or
numerical-honesty work until there is a kernel-checked or explicitly
experimental artifact. The vector-space, duality, module, and tensor part of
that boundary is expanded in
[Linear Algebra Structure Theorem Boundary](linear-algebra-structure-theorem-boundary.md).
The torsion and universal-coefficient part is expanded in
[Chain Complex Torsion Theorem Boundary](chain-complex-torsion-theorem-boundary.md).

## Focused Lessons

- [Matrix Corpus And Benchmark Boundary](matrix-corpus-benchmark-boundary.md)
- [Linear System And LP Replay](linear-system-end-to-end.md)
- [Finite Gaussian Elimination](gaussian-elimination-end-to-end.md)
- [Finite QR Decomposition Checks](qr-decomposition-end-to-end.md)
- [Finite Cholesky Decomposition Checks](cholesky-decomposition-end-to-end.md)
- [Numerical Linear Algebra](numerical-linear-algebra-end-to-end.md)
- [Finite Condition Number](condition-number-end-to-end.md)
- [Finite Schur Complement](schur-complement-end-to-end.md)
- [Finite Singular-Value Shadow](singular-value-shadow-end-to-end.md)
- [Finite Newton Step](newton-step-end-to-end.md)
- [Descriptive Statistics And Regression](descriptive-statistics-regression-end-to-end.md)
- [Rational Inner Product Spaces](inner-product-spaces-end-to-end.md)
- [Finite Walsh-Hadamard Transform Checks](walsh-hadamard-transform-end-to-end.md)
- [Finite Vector Spaces](finite-vector-spaces-end-to-end.md)
- [Finite Dual Spaces](finite-dual-spaces-end-to-end.md)
- [Finite Modules](finite-modules-end-to-end.md)
- [Finite Tensor Products](finite-tensor-products-end-to-end.md)
- [Linear Algebra Structure Theorem Boundary](linear-algebra-structure-theorem-boundary.md)
- [Finite Simplicial Cohomology](finite-simplicial-cohomology-end-to-end.md)
- [Finite Simplicial Cup Products](finite-simplicial-cup-products-end-to-end.md)
- [Finite Chain-Complex Torsion](finite-chain-complex-torsion-end-to-end.md)
- [Chain Complex Torsion Theorem Boundary](chain-complex-torsion-theorem-boundary.md)
- [Finite Universal Coefficient Shadow](finite-universal-coefficient-shadow-end-to-end.md)
- [Spectral Linear Algebra](spectral-linear-algebra-end-to-end.md)
- [Finite Jordan Chain](jordan-chain-end-to-end.md)
- [Matrix Invariants](matrix-invariants-end-to-end.md)
- [Finite Random Matrices](random-matrix-finite-end-to-end.md)
- [Finite Covariance Matrix](covariance-matrix-end-to-end.md)
- [Random Matrix Moment Index](random-matrix-moment-index.md)
- [Finite Simplicial Homology](finite-simplicial-homology-end-to-end.md)
- [Chebyshev And Operator Replay Index](chebyshev-operator-index.md)
- [Finite-Dimensional Operators](finite-operator-end-to-end.md)
- [Finite Chebyshev Systems](finite-chebyshev-systems-end-to-end.md)

Run the route-level checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-algebra-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-gaussian-elimination-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-qr-decomposition-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cholesky-decomposition-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/numerical-linear-algebra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-condition-number-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-schur-complement-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-singular-value-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/inner-product-spaces-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-walsh-hadamard-transform-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-newton-step-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-vector-spaces-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-dual-spaces-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-modules-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-tensor-products-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/spectral-linear-algebra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-jordan-chain-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/matrix-invariants-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/random-matrix-finite-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-covariance-matrix-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/least-squares-regression-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-homology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-chain-complex-torsion-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-cohomology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-universal-coefficient-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-cup-products-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-operator-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-chebyshev-systems-v0
cargo test -p axeyum-solver --test math_resource_lra_routes
cargo test -p axeyum-solver --test math_resource_uf_routes
cargo test -p axeyum-solver --test math_resource_lia_routes
```
