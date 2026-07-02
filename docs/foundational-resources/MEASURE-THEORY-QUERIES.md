# Measure Theory Resource Consumer Queries

This guide turns the finite measure-theory rows in the foundational-resource
JSON contract into copyable downstream queries. It is a consumer-discovery
layer, not a new proof route and not a claim of general measure-theory
coverage.

Use it when a learner page, catalog, solver contributor, or sibling resource
wants to ask:

```text
Which checked finite measure, integration, martingale, or kernel rows match this proof route?
```

The current measure-theory surface is finite and exact-rational: finite
event-algebra tables, complement/additivity/monotonicity/subadditivity rows,
product measures and marginals, simple-function integration, pushforwards,
conditional expectation, tower-property shadows, finite martingales and
bounded stopping rows, stochastic kernels, finite hitting-time equations, and
tail/concentration rows. Sigma-algebras beyond finite tables, countable
additivity, Lebesgue construction, convergence theorems, almost-everywhere
reasoning, martingale convergence, stochastic-process limits, and continuous
probability remain in the proof-horizon lane.

## Query Shape

Start with the field summary:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field measure_theory \
  --route Farkas \
  --require-any
```

Then drill into bridge concepts or checked rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept <bridge_concept_id> \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept <bridge_concept_id> \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Use `packs` for a catalog row or pack path. Use `checks` when the consumer
needs concrete checked rows to display.

## Measure Query Families

| Family | Concept Or Pack Filter | Route Filter | Start Query |
|---|---|---|---|
| Finite measure, complement, monotonicity, subadditivity, normalization, and concentration rows | `bridge_finite_measure_additivity`; `bridge_probability_mass_table` | `Farkas` | `checks --concept bridge_finite_measure_additivity --route Farkas --proof-status checked` |
| Product measure, marginal, integration, and simple-function rows | `bridge_finite_product_integration` | `Farkas` | `checks --concept bridge_finite_product_integration --route Farkas --proof-status checked` |
| Pushforward and expectation-through-pushforward rows | `bridge_pushforward_distribution` | `Farkas` | `checks --concept bridge_pushforward_distribution --route Farkas --proof-status checked` |
| Conditional expectation, total expectation, tower property, and stopped expectation rows | `bridge_conditional_expectation` | `Farkas` | `checks --concept bridge_conditional_expectation --route Farkas --proof-status checked` |
| Stochastic kernels, Markov rows, and finite hitting-time equations | `bridge_stochastic_kernel` | `Farkas` | `checks --concept bridge_stochastic_kernel --route Farkas --proof-status checked` |
| Tail and concentration rows | `bridge_tail_count_obstruction` | `Farkas` | `checks --concept bridge_tail_count_obstruction --route Farkas --proof-status checked` |
| Finite measure display rows | packs `finite-measure-v0`, `finite-measure-monotonicity-v0` | `Farkas` | `checks --pack finite-measure-v0 --route Farkas --proof-status checked`; `checks --pack finite-measure-monotonicity-v0 --route Farkas --proof-status checked` |
| Integration, martingale, and hitting-time display rows | packs `finite-integration-v0`, `finite-martingales-v0`, `finite-hitting-times-v0` | `Farkas` | `checks --pack finite-integration-v0 --route Farkas --proof-status checked --text qf-lra-bad-expectation`; `checks --pack finite-martingales-v0 --route Farkas --proof-status checked --text qf-lra-bad-stopped-expectation`; `checks --pack finite-hitting-times-v0 --route Farkas --proof-status checked --text qf-lra-bad-survival-mass` |

## Copyable Examples

List all promoted finite measure packs:

```sh
python3 scripts/query-foundational-resources.py packs \
  --field measure_theory \
  --route Farkas \
  --require-any
```

Display all checked finite measure rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field measure_theory \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display finite measure additivity, monotonicity, complement, and subadditivity
rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_measure_additivity \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-measure-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-measure-monotonicity-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display product measure and integration rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_product_integration \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-product-measure-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-integration-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-expectation \
  --require-any
```

Display pushforward and conditional-expectation rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_pushforward_distribution \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_conditional_expectation \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display martingale, stochastic-kernel, hitting-time, and concentration rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-martingales-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-stopped-expectation \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text martingale \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-stochastic-kernels-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-hitting-times-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-survival-mass \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-concentration-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

## Current Boundary

These queries prove discoverability of finite checked measure rows, not
theorem coverage. They can support a catalog, learner page, route-specific
regression search, or sibling resource that wants examples by finite measure
object family.

For the finite martingale boundary, read
[Martingale Theorem Boundary](../learn/math/martingale-theorem-boundary.md)
before treating finite filtration, submartingale, bounded-stopping, or checked
bad-row resources as evidence for martingale convergence, optional stopping,
Doob inequalities, stochastic integration, or continuous-time martingales.

They do not prove:

- sigma-algebra construction beyond finite committed tables;
- countable additivity, Lebesgue measure, product-measure existence, or
  almost-everywhere reasoning;
- dominated convergence, monotone convergence, Fubini/Tonelli, or martingale
  convergence theorems;
- stochastic-process limit theorems or continuous-time dynamics;
- floating-point statistical-library behavior or simulation quality;
- benchmark performance, PAR-2, or Z3/cvc5 parity.

Those claims need new proof-horizon rows, theorem-prover reconstruction,
numeric-honesty artifacts, or benchmark evidence before they can graduate.
