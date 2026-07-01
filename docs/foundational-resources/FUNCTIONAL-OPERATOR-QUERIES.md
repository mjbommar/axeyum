# Functional Analysis And Operator Resource Consumer Queries

This guide turns the finite functional-analysis and operator-theory rows in
the foundational-resource JSON contract into copyable downstream queries. It
is a consumer-discovery layer, not a new proof route and not a claim of
infinite-dimensional theorem coverage.

Use it when a learner page, catalog, solver contributor, or sibling resource
wants to ask:

```text
Which checked finite operator, inner-product, spectral, or Chebyshev rows match this proof route?
```

The current surface is finite and exact: matrix/operator norm bounds,
Chebyshev recurrence values, Chebyshev interpolation/residual rows,
inner-product positive-definiteness and projection orthogonality, spectral
eigenpair/Rayleigh checks, characteristic-polynomial and trace rows, and a
small equality-heavy dual/tensor lane. Banach/Hilbert-space theorems, compact
operators, minimax, Haar-space and alternation theorems, topological duals,
and infinite-dimensional approximation claims remain in the proof-horizon
lane.

## Query Shape

Start with the field summary:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field functional_analysis_and_operator_theory \
  --route Farkas \
  --require-any
```

Then drill into bridge concepts or checked rows:

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

Use `Farkas` for exact rational operator, Chebyshev, inner-product, and
spectral rows. Use `Alethe` for finite dual/tensor equality rows.

## Functional/Operator Query Families

| Family | Concept Or Pack Filter | Route Filter | Start Query |
|---|---|---|---|
| Finite operator, Chebyshev, trace, characteristic-polynomial, and spectral replay | `bridge_finite_operator_chebyshev` | `Farkas` | `checks --concept bridge_finite_operator_chebyshev --route Farkas --proof-status checked` |
| Eigenpair, Rayleigh, operator, inner-product, and invariant rows | `bridge_eigenpair` | `Farkas` | `checks --concept bridge_eigenpair --route Farkas --proof-status checked` |
| Inner-product and projection rows | `bridge_inner_product_projection` | `Farkas` | `checks --concept bridge_inner_product_projection --route Farkas --proof-status checked` |
| Dual, tensor, subspace, and module equality rows | `bridge_tensor_bilinearity` | `Alethe` | `checks --concept bridge_tensor_bilinearity --route Alethe --proof-status checked` |
| Operator display rows | pack `finite-operator-v0` | `Farkas` | `checks --pack finite-operator-v0 --route Farkas --proof-status checked` |
| Chebyshev-system display rows | pack `finite-chebyshev-systems-v0` | `Farkas` | `checks --pack finite-chebyshev-systems-v0 --route Farkas --proof-status checked` |
| Spectral display rows | pack `spectral-linear-algebra-v0` | `Farkas` | `checks --pack spectral-linear-algebra-v0 --route Farkas --proof-status checked` |
| Dual-space additivity certificate rows | pack `finite-dual-spaces-v0` | `Alethe` | `checks --pack finite-dual-spaces-v0 --route Alethe --proof-status checked --text additivity` |

## Copyable Examples

List all promoted functional-analysis/operator packs on the Farkas route:

```sh
python3 scripts/query-foundational-resources.py packs \
  --field functional_analysis_and_operator_theory \
  --route Farkas \
  --require-any
```

Display all checked Farkas rows for this field:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field functional_analysis_and_operator_theory \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display finite operator, Chebyshev, spectral, trace, and characteristic
polynomial rows through their shared bridge:

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

Display eigenpair, Rayleigh, operator, and invariant rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_eigenpair \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display inner-product and projection rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_inner_product_projection \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display dual/tensor equality rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_tensor_bilinearity \
  --route Alethe \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_tensor_bilinearity \
  --route Alethe \
  --proof-status checked \
  --require-any
```

For focused UI cards, query individual packs:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-operator-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-chebyshev-systems-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack spectral-linear-algebra-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack inner-product-spaces-rational-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-dual-spaces-v0 \
  --route Alethe \
  --proof-status checked \
  --text additivity \
  --require-any
```

## Current Boundary

These queries prove discoverability of finite checked functional/operator
rows, not theorem coverage. They can support a catalog, learner page,
route-specific regression search, or sibling resource that wants examples by
finite operator family.

They do not prove:

- Banach-space, Hilbert-space, compact-operator, or topological-dual theorem
  schemas;
- minimax, Hahn-Banach, spectral-theorem, Haar-space, Chebyshev alternation, or
  infinite-dimensional approximation theorems;
- conditioning, stability, floating-point, or asymptotic numerical-analysis
  guarantees;
- benchmark performance, PAR-2, or Z3/cvc5 parity.

Those claims need new proof-horizon rows, theorem-prover reconstruction,
numerical-analysis artifacts, or benchmark evidence before they can graduate.
