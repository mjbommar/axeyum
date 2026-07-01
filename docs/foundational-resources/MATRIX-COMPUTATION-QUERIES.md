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
| Linear systems and LU | `bridge_lu_replay` | `Farkas` | `packs --concept bridge_lu_replay --route Farkas` |
| Residual bounds and least squares | `bridge_residual_bound` | `Farkas` | `checks --concept bridge_residual_bound --route Farkas --proof-status checked` |
| Rank, kernel, image, and dual rows | `bridge_rank_nullity` | `Alethe` | `packs --concept bridge_rank_nullity --route Alethe` |
| Eigenpairs and matrix invariants | `bridge_eigenpair` | `Farkas` | `checks --concept bridge_eigenpair --route Farkas --proof-status checked` |
| Finite random-matrix moments | `bridge_random_matrix_finite_moment` | `Farkas` | `packs --concept bridge_random_matrix_finite_moment --route Farkas` |
| Inner products and projections | `bridge_inner_product_projection` | `Farkas` | `checks --concept bridge_inner_product_projection --route Farkas --proof-status checked` |
| Integer chain-complex torsion | `bridge_finite_torsion_homology_replay` | `Diophantine` | `checks --concept bridge_finite_torsion_homology_replay --route Diophantine --proof-status checked` |
| Universal-coefficient shadow | `bridge_finite_universal_coefficient_shadow` | `Alethe` | `checks --concept bridge_finite_universal_coefficient_shadow --route Alethe --proof-status checked` |
| Modules and tensor bilinearity | `bridge_tensor_bilinearity` | `Alethe` | `packs --concept bridge_tensor_bilinearity --route Alethe` |
| Operators and Chebyshev systems | `bridge_finite_operator_chebyshev` | `Farkas` | `packs --concept bridge_finite_operator_chebyshev --route Farkas` |

## Copyable Examples

List the finite LU/linear-system packs that have Farkas-route pressure:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_lu_replay \
  --route Farkas \
  --require-any
```

Display checked residual-bound rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_residual_bound \
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
```

Display checked eigenpair or matrix-invariant rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_eigenpair \
  --route Farkas \
  --proof-status checked \
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
```

## Boundary

These queries prove discoverability, not theorem coverage. They can support a
catalog, a learner page, a route-specific regression search, or a sibling
resource that wants examples by computation type.

They do not prove:

- general rank-nullity, spectral, Hilbert-space, Chebyshev, Smith-normal-form,
  universal-coefficient, or homology theorems;
- floating-point stability, conditioning, or convergence of numerical methods;
- random-matrix asymptotics or simulation quality;
- benchmark performance, PAR-2, or Z3/cvc5 parity.

Those claims need the proof-horizon or benchmarking artifacts named in
[Matrix Corpus And Benchmark Boundary](../learn/math/matrix-corpus-benchmark-boundary.md).
