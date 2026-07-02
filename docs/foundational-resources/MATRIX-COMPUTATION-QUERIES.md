# Matrix Computation Consumer Queries

This guide turns the matrix rows in
[Matrix Computation Index](../learn/math/matrix-computation-index.md) into
copyable downstream queries over the public foundational-resource JSON
contract. It is a consumer-discovery layer, not a new proof route and not a
benchmark claim.

Use it when a learner page, solver contributor, or sibling resource wants to
ask:

```text
Which checked matrix packs match this computation family and this proof route?
```

The implementation is intentionally small: `query-foundational-resources.py`
supports exact atlas concept filters on pack and check queries. Concept
membership comes from
[`artifacts/ontology/foundational-concepts.json`](../../artifacts/ontology/foundational-concepts.json),
while proof-route and checked-row filters still come from committed pack
metadata and expected-result rows.

## Query Shape

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept <bridge_concept_id> \
  --route <route-substring> \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept <bridge_concept_id> \
  --route <route-substring> \
  --proof-status checked \
  --require-any
```

Use `packs` when a consumer needs a catalog row or pack path. Use `checks`
when the consumer needs a concrete checked row to display.

## Matrix Computation Queries

| Computation Family | Concept Filter | Route Filter | Start Query |
|---|---|---|---|
| Linear systems, Gaussian elimination, nullspaces, LU, QR, Givens, Householder, and Cholesky | `bridge_lu_replay`; packs `linear-algebra-rational-v0`, `finite-gaussian-elimination-v0`, `finite-qr-decomposition-v0`, `finite-givens-rotation-v0`, `finite-householder-reflection-v0`, `finite-cholesky-decomposition-v0` | `Farkas` | `checks --concept bridge_lu_replay --route Farkas --proof-status checked`; `checks --pack finite-gaussian-elimination-v0 --route Farkas --proof-status checked`; `checks --pack linear-algebra-rational-v0 --route Farkas --proof-status checked --text nullspace`; `checks --pack linear-algebra-rational-v0 --route Farkas --proof-status checked --text product-entry`; `checks --pack finite-qr-decomposition-v0 --route Farkas --proof-status checked`; `checks --pack finite-givens-rotation-v0 --route Farkas --proof-status checked`; `checks --pack finite-householder-reflection-v0 --route Farkas --proof-status checked`; `checks --pack finite-cholesky-decomposition-v0 --route Farkas --proof-status checked` |
| Schur complements and block matrix shadows | `bridge_schur_complement`; pack `finite-schur-complement-v0` | `Farkas` | `packs --concept bridge_schur_complement --route Farkas`; `checks --concept bridge_schur_complement --route Farkas --proof-status checked`; `checks --pack finite-schur-complement-v0 --route Farkas --proof-status checked` |
| Residual bounds, condition numbers, singular values, power iteration, conjugate gradient, Arnoldi, Lanczos, Hessian solves, solution boxes, and least squares | `bridge_residual_bound`; packs `numerical-linear-algebra-v0`, `finite-condition-number-v0`, `finite-singular-value-shadow-v0`, `finite-power-iteration-v0`, `finite-conjugate-gradient-v0`, `finite-arnoldi-iteration-v0`, `finite-lanczos-iteration-v0`, `finite-newton-step-v0` | `Farkas` | `checks --concept bridge_residual_bound --route Farkas --proof-status checked`; `checks --pack finite-condition-number-v0 --route Farkas --proof-status checked`; `checks --pack finite-singular-value-shadow-v0 --route Farkas --proof-status checked`; `checks --pack finite-power-iteration-v0 --route Farkas --proof-status checked`; `checks --pack finite-conjugate-gradient-v0 --route Farkas --proof-status checked`; `checks --pack finite-arnoldi-iteration-v0 --route Farkas --proof-status checked`; `checks --pack finite-lanczos-iteration-v0 --route Farkas --proof-status checked`; `checks --pack finite-newton-step-v0 --route Farkas --proof-status checked`; `checks --pack numerical-linear-algebra-v0 --route Farkas --proof-status checked --text solution` |
| Rank, kernel, image, vector-space, and dual rows | `bridge_rank_nullity`; pack `finite-vector-spaces-v0` | `Alethe` | `packs --concept bridge_rank_nullity --route Alethe`; `checks --pack finite-vector-spaces-v0 --route Alethe --proof-status checked --text addition-closure` |
| Rayleigh quotients, eigenpairs, power iteration, Arnoldi/Hessenberg, Lanczos/tridiagonal, Jordan chains, singular values, and matrix invariants | `bridge_eigenpair` | `Farkas` | `checks --concept bridge_eigenpair --route Farkas --proof-status checked`; `checks --pack finite-power-iteration-v0 --route Farkas --proof-status checked`; `checks --pack finite-arnoldi-iteration-v0 --route Farkas --proof-status checked`; `checks --pack finite-lanczos-iteration-v0 --route Farkas --proof-status checked`; `checks --pack finite-jordan-chain-v0 --route Farkas --proof-status checked`; `checks --pack finite-singular-value-shadow-v0 --route Farkas --proof-status checked` |
| Orthogonal transforms, Givens rotations, Householder reflections, and Parseval scaling | `bridge_inner_product_projection`; packs `finite-walsh-hadamard-transform-v0`, `finite-givens-rotation-v0`, `finite-householder-reflection-v0` | `Farkas` | `checks --pack finite-walsh-hadamard-transform-v0 --route Farkas --proof-status checked`; `checks --pack finite-givens-rotation-v0 --route Farkas --proof-status checked`; `checks --pack finite-householder-reflection-v0 --route Farkas --proof-status checked`; `checks --concept bridge_inner_product_projection --route Farkas --proof-status checked --text transform`; `checks --concept bridge_inner_product_projection --route Farkas --proof-status checked --text Givens`; `checks --concept bridge_inner_product_projection --route Farkas --proof-status checked --text Householder` |
| Finite random-matrix moments, ranks, and covariance | `bridge_random_matrix_finite_moment` | `Farkas` | `checks --pack random-matrix-finite-v0 --route Farkas --proof-status checked --text rank`; `checks --pack finite-covariance-matrix-v0 --route Farkas --proof-status checked` |
| Inner products and projections | `bridge_inner_product_projection` | `Farkas` | `checks --concept bridge_inner_product_projection --route Farkas --proof-status checked` |
| Integer chain-complex torsion | `bridge_finite_torsion_homology_replay` | `Diophantine` | `checks --concept bridge_finite_torsion_homology_replay --route Diophantine --proof-status checked` |
| Universal-coefficient shadow | `bridge_finite_universal_coefficient_shadow` | `Alethe` | `checks --concept bridge_finite_universal_coefficient_shadow --route Alethe --proof-status checked` |
| Modules and tensor bilinearity | `bridge_tensor_bilinearity`; packs `finite-modules-v0`, `finite-tensor-products-v0` | `Alethe` | `packs --concept bridge_tensor_bilinearity --route Alethe`; `checks --pack finite-modules-v0 --route Alethe --proof-status checked --text scalar-closure`; `checks --pack finite-tensor-products-v0 --route Alethe --proof-status checked --text left-additivity` |
| Operators and Chebyshev systems | `bridge_finite_operator_chebyshev` | `Farkas` | `checks --pack finite-operator-v0 --route Farkas --proof-status checked --text qf-lra-bad-chebyshev-t3` |

## Copyable Examples

Display checked finite LU/linear-system rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_lu_replay \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack linear-algebra-rational-v0 \
  --route Farkas \
  --proof-status checked \
  --text nullspace \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack linear-algebra-rational-v0 \
  --route Farkas \
  --proof-status checked \
  --text product-entry \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-gaussian-elimination-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked residual-bound rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_residual_bound \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack numerical-linear-algebra-v0 \
  --route Farkas \
  --proof-status checked \
  --text solution \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-condition-number-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-singular-value-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-power-iteration-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-conjugate-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-arnoldi-iteration-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-lanczos-iteration-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-newton-step-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked Schur-complement rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_schur_complement \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_schur_complement \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-schur-complement-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

List equality-heavy rank/nullity packs that use the Alethe route:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_rank_nullity \
  --route Alethe \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-vector-spaces-v0 \
  --route Alethe \
  --proof-status checked \
  --text addition-closure \
  --require-any
```

Display checked Rayleigh, eigenpair, Jordan-chain, singular-value, or
matrix-invariant rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_eigenpair \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-singular-value-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-power-iteration-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-arnoldi-iteration-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-lanczos-iteration-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-jordan-chain-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked finite QR product-entry rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-qr-decomposition-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked finite Givens sine-coefficient rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-givens-rotation-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked finite Householder entry rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-householder-reflection-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked finite Cholesky product-entry rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-cholesky-decomposition-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked finite Walsh-Hadamard transform rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-walsh-hadamard-transform-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_inner_product_projection \
  --route Farkas \
  --proof-status checked \
  --text transform \
  --require-any
```

List finite random-matrix packs with exact-rational route pressure:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_random_matrix_finite_moment \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_random_matrix_finite_moment \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack random-matrix-finite-v0 \
  --route Farkas \
  --proof-status checked \
  --text rank \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-covariance-matrix-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked finite torsion-homology matrix rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_torsion_homology_replay \
  --route Diophantine \
  --proof-status checked \
  --require-any
```

Display checked finite universal-coefficient shadow rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_universal_coefficient_shadow \
  --route Alethe \
  --proof-status checked \
  --require-any
```

List finite tensor/module packs that use the equality route:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_tensor_bilinearity \
  --route Alethe \
  --require-any
```

List finite operator and Chebyshev-system packs with Farkas-route rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_operator_chebyshev \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_operator_chebyshev \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-operator-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-chebyshev-t3 \
  --require-any
```

## Boundary

These queries prove discoverability, not theorem coverage. They can support a
catalog, a learner page, a route-specific regression search, or a sibling
resource that wants examples by computation type.

They do not prove:

- general rank-nullity, Schur-complement, block-inverse, spectral, SVD, Jordan-normal-form,
  diagonalizability, Hilbert-space, Chebyshev, Smith-normal-form,
  universal-coefficient, or homology theorems;
- floating-point stability, singular-value perturbation, conditioning, or
  convergence of numerical methods;
- random-matrix asymptotics or simulation quality;
- benchmark performance, PAR-2, or Z3/cvc5 parity.

Those claims need the proof-horizon or benchmarking artifacts named in
[Matrix Corpus And Benchmark Boundary](../learn/math/matrix-corpus-benchmark-boundary.md).
