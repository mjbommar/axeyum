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

Concept rows:

- `bridge_lu_replay`, `bridge_rank_nullity`, `bridge_residual_bound`,
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
| Linear systems and LU | [linear-algebra-rational-v0](../../../artifacts/examples/math/linear-algebra-rational-v0/), [linear-optimization-v0](../../../artifacts/examples/math/linear-optimization-v0/) | Fixed `A*x = b`, `L*U = A`, bad LU product-entry rejection, singular-row inconsistency, LP objective thresholds | finite replay plus QF_LRA/Farkas |
| Residuals and numerical shadows | [numerical-linear-algebra-v0](../../../artifacts/examples/math/numerical-linear-algebra-v0/), [least-squares-regression-v0](../../../artifacts/examples/math/least-squares-regression-v0/) | Exact residual norms, solution boxes, one Jacobi step, normal equations, residual orthogonality | finite replay plus QF_LRA/Farkas |
| Inner products and projections | [inner-product-spaces-rational-v0](../../../artifacts/examples/math/inner-product-spaces-rational-v0/) | Gram matrices, fixed Cauchy-Schwarz, orthogonal projection, Gram-Schmidt, bad negative norm, bad projection orthogonality | finite replay plus QF_LRA/Farkas |
| Kernel, image, rank, and duals | [finite-vector-spaces-v0](../../../artifacts/examples/math/finite-vector-spaces-v0/), [finite-dual-spaces-v0](../../../artifacts/examples/math/finite-dual-spaces-v0/) | Finite `F2` vector-space tables, subspaces, linear maps, kernel/image, rank-nullity, covectors, annihilators, transpose maps | finite table replay plus QF_UF/Alethe |
| Modules and tensors | [finite-modules-v0](../../../artifacts/examples/math/finite-modules-v0/), [finite-tensor-products-v0](../../../artifacts/examples/math/finite-tensor-products-v0/) | Scalar actions, generated submodules, module homomorphisms, quotients, bilinear maps, tensor basis rows, Kronecker products | finite table replay plus QF_UF/Alethe |
| Spectral rows | [spectral-linear-algebra-v0](../../../artifacts/examples/math/spectral-linear-algebra-v0/), [matrix-invariants-v0](../../../artifacts/examples/math/matrix-invariants-v0/) | Eigenpairs, orthogonal eigenbasis arithmetic, Rayleigh quotients, bad Rayleigh quotients, spectral reconstruction, trace, determinant, characteristic roots, Cayley-Hamilton, Gershgorin intervals, bad trace and bad characteristic-polynomial rows | finite replay plus QF_LRA/Farkas |
| Random matrices | [random-matrix-finite-v0](../../../artifacts/examples/math/random-matrix-finite-v0/) | Finite matrix-valued probability tables, trace/determinant moments, expected Gram matrices, rank mixture probabilities | finite expectation replay plus QF_LRA/Farkas |
| Chain, cochain, cup-product, and torsion matrices | [finite-simplicial-homology-v0](../../../artifacts/examples/math/finite-simplicial-homology-v0/), [finite-chain-complex-torsion-v0](../../../artifacts/examples/math/finite-chain-complex-torsion-v0/), [finite-simplicial-cohomology-v0](../../../artifacts/examples/math/finite-simplicial-cohomology-v0/), [finite-universal-coefficient-shadow-v0](../../../artifacts/examples/math/finite-universal-coefficient-shadow-v0/), [finite-simplicial-cup-products-v0](../../../artifacts/examples/math/finite-simplicial-cup-products-v0/) | Boundary matrices, boundary squared, Betti-rank replay, one-entry Smith diagonal replay, `Z/2` torsion quotient, integer dual cochain maps, finite Hom/Ext shadow bookkeeping, F2 coboundary matrices, cohomology-rank replay, finite F2 cup-product table replay, bad oriented-boundary coefficient, bad torsion generator, bad `H^1 = 0`, bad coboundary value, bad cup-product value | finite replay plus QF_LIA/Diophantine, QF_UF/Alethe, or QF_BV/DRAT |
| Operators and interpolation matrices | [finite-operator-v0](../../../artifacts/examples/math/finite-operator-v0/), [finite-chebyshev-systems-v0](../../../artifacts/examples/math/finite-chebyshev-systems-v0/) | Operator norm bounds, matrix action, Chebyshev recurrence, Vandermonde unisolvence, interpolation values, alternating residuals | finite replay plus QF_LRA/Farkas |

## What The Checker Trusts

For exact rational rows, the trusted work is small arithmetic: matrix-vector
multiplication, matrix multiplication, determinant or trace formulas for the
fixed dimension, exact residuals, rational inequalities, and Farkas certificate
checking when a row is unsatisfiable. The LU slice now has both a positive
`L*U = A` replay row and a checked bad product-entry row, so consumers can see
the replay/certificate boundary without leaving the core matrix pack.

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

The finite rows do not prove general rank-nullity, spectral theorem,
Cayley-Hamilton over arbitrary rings, Hilbert projection, Riesz representation,
Hahn-Banach, stability or conditioning of numerical algorithms, asymptotic
random-matrix laws, minimax approximation, general Smith normal form,
classification of finitely generated abelian groups, homology invariance,
universal coefficient theorems, exact sequences, Ext/Tor laws, cohomology
operation laws, cohomology-ring quotienting, or cohomology invariance. Those
claims remain Lean-horizon or
numerical-honesty work until there is a kernel-checked or explicitly
experimental artifact.

## Focused Lessons

- [Matrix Corpus And Benchmark Boundary](matrix-corpus-benchmark-boundary.md)
- [Linear System And LP Replay](linear-system-end-to-end.md)
- [Numerical Linear Algebra](numerical-linear-algebra-end-to-end.md)
- [Descriptive Statistics And Regression](descriptive-statistics-regression-end-to-end.md)
- [Rational Inner Product Spaces](inner-product-spaces-end-to-end.md)
- [Finite Vector Spaces](finite-vector-spaces-end-to-end.md)
- [Finite Dual Spaces](finite-dual-spaces-end-to-end.md)
- [Finite Modules](finite-modules-end-to-end.md)
- [Finite Tensor Products](finite-tensor-products-end-to-end.md)
- [Finite Simplicial Cohomology](finite-simplicial-cohomology-end-to-end.md)
- [Finite Simplicial Cup Products](finite-simplicial-cup-products-end-to-end.md)
- [Finite Chain-Complex Torsion](finite-chain-complex-torsion-end-to-end.md)
- [Finite Universal Coefficient Shadow](finite-universal-coefficient-shadow-end-to-end.md)
- [Spectral Linear Algebra](spectral-linear-algebra-end-to-end.md)
- [Matrix Invariants](matrix-invariants-end-to-end.md)
- [Finite Random Matrices](random-matrix-finite-end-to-end.md)
- [Random Matrix Moment Index](random-matrix-moment-index.md)
- [Finite Simplicial Homology](finite-simplicial-homology-end-to-end.md)
- [Chebyshev And Operator Replay Index](chebyshev-operator-index.md)
- [Finite-Dimensional Operators](finite-operator-end-to-end.md)
- [Finite Chebyshev Systems](finite-chebyshev-systems-end-to-end.md)

Run the route-level checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-algebra-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/numerical-linear-algebra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/inner-product-spaces-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-vector-spaces-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-dual-spaces-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-modules-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-tensor-products-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/spectral-linear-algebra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/matrix-invariants-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/random-matrix-finite-v0
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
