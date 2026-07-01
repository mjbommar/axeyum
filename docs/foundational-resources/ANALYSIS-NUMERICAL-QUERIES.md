# Analysis And Numerical Resource Consumer Queries

This guide turns the real-analysis, numerical-analysis, and complex-analysis
rows in the foundational-resource JSON contract into copyable downstream
queries. It is a consumer-discovery layer, not a new proof route and not a
claim of theorem-level analysis coverage.

Use it when a learner page, catalog, solver contributor, or sibling resource
wants to ask:

```text
Which checked finite analysis, numerical, or complex rows match this proof route?
```

The current surface is finite and exact-rational: metric balls, bounded
epsilon-delta shadows, bounded sequence tails, algebraic derivative and
integral replay, Newton/root-finding steps, finite recurrence and Euler rows,
residual/Jacobi rows, exact-vs-floating boundary rows, and complex numbers as
real-pair algebra. Completeness, IVT/MVT/FTC, uniform convergence, analytic
continuation, holomorphicity, contour integration, numerical stability, and
floating-point error guarantees remain in the proof-horizon or
numerical-honesty lanes.

## Query Shape

Start with field summaries:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field real_analysis \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field numerical_analysis \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field complex_analysis \
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

## Analysis And Numerical Query Families

| Family | Concept Or Pack Filter | Route Filter | Start Query |
|---|---|---|---|
| Metric balls and bounded epsilon-delta rows | `bridge_metric_ball`; `bridge_bounded_epsilon_delta_shadow` | `Farkas` | `checks --concept bridge_bounded_epsilon_delta_shadow --route Farkas --proof-status checked` |
| Algebraic derivative and Riemann-sum shadows | packs `calculus-algebraic-shadow-v0`, `calculus-riemann-sum-v0` | `Farkas` | `checks --pack calculus-algebraic-shadow-v0 --route Farkas --proof-status checked`; `checks --pack calculus-riemann-sum-v0 --route Farkas --proof-status checked` |
| Root-finding and Newton-step rows | pack `finite-root-finding-v0`; concept `bridge_exact_vs_floating_arithmetic` | `Farkas` | `checks --pack finite-root-finding-v0 --route Farkas --proof-status checked` |
| Finite dynamics, recurrence, and Euler replay | `bridge_finite_dynamics_euler_replay` | `Farkas` | `checks --concept bridge_finite_dynamics_euler_replay --route Farkas --proof-status checked` |
| Residuals, Jacobi steps, and numerical linear algebra | `bridge_residual_bound`; `bridge_lu_replay` | `Farkas` | `checks --concept bridge_residual_bound --route Farkas --proof-status checked`; `checks --pack numerical-linear-algebra-v0 --route Farkas --proof-status checked` |
| Operator/Chebyshev and spectral numerical rows | `bridge_finite_operator_chebyshev`; `bridge_eigenpair` | `Farkas` | `checks --concept bridge_finite_operator_chebyshev --route Farkas --proof-status checked`; `checks --concept bridge_eigenpair --route Farkas --proof-status checked` |
| Complex numbers and plane transforms as real-pair algebra | `bridge_complex_real_pair_transform` | `Farkas` | `checks --concept bridge_complex_real_pair_transform --route Farkas --proof-status checked` |
| Exact-vs-floating boundary rows | `bridge_exact_vs_floating_arithmetic` | `Farkas` | `checks --concept bridge_exact_vs_floating_arithmetic --route Farkas --proof-status checked` |

## Copyable Examples

Display checked bounded epsilon-delta and finite sequence-tail rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_bounded_epsilon_delta_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked finite recurrence-prefix rows, including affine-step
refutations:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-recurrence-prefix-v0 \
  --route Farkas \
  --proof-status checked \
  --text affine \
  --require-any
```

Display checked metric-ball rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_metric_ball \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_metric_ball \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked algebraic derivative, integral, and root-finding rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack calculus-algebraic-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack calculus-riemann-sum-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-root-finding-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-root-finding-v0 \
  --route Farkas \
  --proof-status checked \
  --text width \
  --require-any
```

Display checked finite dynamics, recurrence, and Euler rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_dynamics_euler_replay \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked numerical linear algebra rows:

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
  --require-any
```

Display checked complex real-pair rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_complex_real_pair_transform \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_complex_real_pair_transform \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked exact-vs-floating boundary rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_exact_vs_floating_arithmetic \
  --route Farkas \
  --proof-status checked \
  --require-any
```

For focused UI cards, query individual analysis and numerical packs:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack metric-continuity-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack sequence-limit-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack bounded-monotone-sequence-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack bounded-monotone-sequence-v0 \
  --route Farkas \
  --proof-status checked \
  --text tail \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-euler-method-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack complex-algebraic-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

## Current Boundary

These queries prove discoverability of finite checked analysis, numerical, and
complex rows, not theorem coverage. They can support a catalog, learner page,
route-specific regression search, or sibling resource that wants examples by
finite analytic object family.

They do not prove:

- completeness, IVT/MVT/FTC, compactness, or arbitrary convergence theorems;
- theorem-level epsilon-delta calculus beyond the finite bounded rows;
- numerical stability, conditioning, floating-point error bounds, or
  performance claims;
- holomorphicity, Cauchy theory, residues, contour integration, analytic
  continuation, or algebraic closure;
- benchmark performance, PAR-2, or Z3/cvc5 parity.

Those claims need new proof-horizon rows, theorem-prover reconstruction,
numerical-analysis artifacts, or benchmark evidence before they can graduate.
