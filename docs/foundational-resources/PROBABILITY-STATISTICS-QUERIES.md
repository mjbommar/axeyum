# Probability And Statistics Resource Consumer Queries

This guide turns the finite probability, measure, stochastic-process, and
statistics rows in the foundational-resource JSON contract into copyable
downstream queries. It is a consumer-discovery layer, not a new proof route and
not a claim of continuous probability, asymptotic statistics, or inference
coverage.

Use it when a learner page, catalog, solver contributor, or sibling resource
wants to ask:

```text
Which checked finite-table probability or statistics packs match this proof route?
```

The current probability/statistics surface is finite and exact-rational:
probability mass tables, finite measure additivity, product measures,
pushforward distributions, simple-function integration, conditional
expectation, finite martingale/stopping rows, finite distribution-distance
rows, stochastic kernels, finite Markov chains, finite hitting times,
concentration/tail-count rows, exact tests, and finite random-matrix moments.
Continuous distributions, sampling guarantees, asymptotic inference, MCMC/VI,
stochastic-process limits, random-matrix limit laws, and floating-point
statistical-library behavior remain in proof-horizon or numerical-honesty
lanes.

## Query Shape

Start with field summaries by route:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field probability_theory \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field measure_theory \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field statistics \
  --route Farkas \
  --require-any
```

Then drill into bridge concepts by finite-table family:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_probability_mass_table \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_tail_count_obstruction \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Use `packs` for catalog rows and pack paths. Use `checks` when the consumer
needs concrete checked rows to display.

## Probability Query Families

| Family | Concept Filter | Route Filter | Start Query |
|---|---|---|---|
| Probability mass, finite measure, normalization, Bayes, independence, total variation, and concentration rows | `bridge_probability_mass_table` | `Farkas` | `checks --concept bridge_probability_mass_table --route Farkas --proof-status checked` |
| Finite measure additivity, monotonicity, complement, and subadditivity rows | `bridge_finite_measure_additivity` | `Farkas` | `checks --concept bridge_finite_measure_additivity --route Farkas --proof-status checked` |
| Product measure, simple integration, conditional expectation, and martingale rows | `bridge_finite_product_integration` | `Farkas` | `checks --concept bridge_finite_product_integration --route Farkas --proof-status checked` |
| Pushforward distributions and expectation-through-pushforward rows | `bridge_pushforward_distribution` | `Farkas` | `checks --concept bridge_pushforward_distribution --route Farkas --proof-status checked` |
| Conditional expectation, total expectation, tower property, and stopped expectation rows | `bridge_conditional_expectation` | `Farkas` | `checks --concept bridge_conditional_expectation --route Farkas --proof-status checked` |
| Stochastic kernels, finite Markov chains, hitting times, and recurrence rows | `bridge_stochastic_kernel` | `Farkas` | `checks --concept bridge_stochastic_kernel --route Farkas --proof-status checked` |
| Tail counts, exact tests, finite concentration, and variance rows | `bridge_tail_count_obstruction` | `Farkas` | `checks --concept bridge_tail_count_obstruction --route Farkas --proof-status checked` |
| Random-matrix finite moments and expected-rank rows | `bridge_random_matrix_finite_moment` | `Farkas` | `checks --concept bridge_random_matrix_finite_moment --route Farkas --proof-status checked` |

## Copyable Examples

Display checked finite probability rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field probability_theory \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked finite distribution-distance rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-probability-v0 \
  --route Farkas \
  --proof-status checked \
  --text "total variation" \
  --require-any
```

Display finite Bayes update rows, then the checked malformed-posterior row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-probability-v0 \
  --text Bayes \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-probability-v0 \
  --text Bayes \
  --proof-status checked \
  --require-any
```

Display finite concentration rows, then the theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-concentration-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text concentration \
  --require-any
```

Display checked finite measure rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field measure_theory \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked statistics rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field statistics \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display finite probability-mass and finite-measure table rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_probability_mass_table \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_measure_additivity \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display product, integration, pushforward, and conditional-expectation rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_product_integration \
  --route Farkas \
  --proof-status checked \
  --require-any

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

Display stochastic-kernel, tail-count, and random-matrix rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_stochastic_kernel \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_tail_count_obstruction \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_random_matrix_finite_moment \
  --route Farkas \
  --proof-status checked \
  --require-any
```

## Current Boundary

These queries prove discoverability of finite checked probability/statistics
rows, not theorem coverage. They can support a catalog, learner page,
solver-regression search, or sibling resource that needs examples by finite
probability object family.

For the finite concentration boundary in particular, read
[Concentration Theorem Boundary](../learn/math/concentration-theorem-boundary.md)
before displaying Chernoff, Hoeffding, martingale concentration, limit-theorem,
or asymptotic-statistics language next to the finite rows.

They do not prove:

- continuous distributions, density calculus, or measure construction;
- countable additivity beyond committed finite tables;
- convergence theorems, laws of large numbers, CLT, or martingale convergence;
- statistical inference guarantees, sampling quality, MCMC, VI, or model
  calibration;
- random-matrix asymptotics, universality, or concentration theorems;
- floating-point statistical-library behavior;
- benchmark performance, PAR-2, or Z3/cvc5 parity.

Those claims need new proof-horizon rows, theorem-prover reconstruction,
numeric-honesty artifacts, or benchmark evidence before they can graduate.
