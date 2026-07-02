# Optimization And Convexity Resource Consumer Queries

This guide turns the finite optimization and convexity rows in the
foundational-resource JSON contract into copyable downstream queries. It is a
consumer-discovery layer, not a new proof route and not an optimization
theorem claim.

Use it when a learner page, catalog, solver contributor, or sibling resource
wants to ask:

```text
Which checked optimization packs match this finite method family and proof route?
```

The current optimization surface is finite and exact-rational: LP objective
thresholds, convexity shadows, finite separation, KKT stationarity and
complementarity, active-set QP face/slack and degenerate-bound replay, tiny SDP
objective/slack/gap replay, gradient-descent steps, Armijo/Wolfe line-search
rows, projected-gradient interval/decrease replay, proximal-gradient soft-threshold and
composite-decrease plus box-plus-L1 replay, least-squares rows, residual bounds, and projection
witnesses. General duality, KKT sufficiency, SDP strong duality, method
convergence, stability, and floating-point performance claims remain in the
proof-horizon or numerical-honesty lanes.

## Query Shape

Start with the field summary:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field optimization_and_convexity \
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

## Optimization Query Families

| Optimization Family | Concept Or Pack Filter | Route Filter | Start Query |
|---|---|---|---|
| LP objective thresholds and Farkas anatomy | `bridge_lp_objective_farkas` | `Farkas` | `checks --concept bridge_lp_objective_farkas --route Farkas --proof-status checked` |
| Convexity, separation, KKT, QP, SDP, and finite first-order method shadows | `bridge_rational_convexity_shadow` | `Farkas` | `checks --concept bridge_rational_convexity_shadow --route Farkas --proof-status checked` |
| Affine-threshold convexity display row | pack `convexity-rational-v0`, text `threshold` | `Farkas` | `checks --pack convexity-rational-v0 --route Farkas --proof-status checked --text threshold` |
| Inner-product projection and least-squares optimality rows | `bridge_inner_product_projection` | `Farkas` | `checks --concept bridge_inner_product_projection --route Farkas --proof-status checked` |
| Residual bounds and regression/numerical optimization rows | `bridge_residual_bound` | `Farkas` | `checks --concept bridge_residual_bound --route Farkas --proof-status checked` |
| Exact arithmetic and numerical-honesty rows | `bridge_exact_vs_floating_arithmetic` | `Farkas` | `checks --concept bridge_exact_vs_floating_arithmetic --route Farkas --proof-status checked` |
| KKT stationarity and complementarity display rows | pack `finite-kkt-v0` | `Farkas` | `checks --pack finite-kkt-v0 --route Farkas --proof-status checked` |
| Active-set QP display row | pack `finite-active-set-qp-v0` | `Farkas` | `checks --pack finite-active-set-qp-v0 --route Farkas --proof-status checked` |
| Inactive active-set slack row | pack `finite-active-set-qp-v0`, text `inactive` | `Farkas` | `checks --pack finite-active-set-qp-v0 --route Farkas --proof-status checked --text inactive` |
| Degenerate active-set multiplier row | pack `finite-active-set-qp-v0`, text `degenerate` | `Farkas` | `checks --pack finite-active-set-qp-v0 --route Farkas --proof-status checked --text degenerate` |
| SDP objective/slack/gap display row | pack `finite-sdp-v0` | `Farkas` | `checks --pack finite-sdp-v0 --route Farkas --proof-status checked`; `checks --pack finite-sdp-v0 --route Farkas --proof-status checked --text slack` |
| Gradient descent and line-search display rows | packs `finite-gradient-descent-v0`, `finite-line-search-v0`, `finite-wolfe-line-search-v0` | `Farkas` | `checks --pack finite-gradient-descent-v0 --route Farkas --proof-status checked`; `checks --pack finite-line-search-v0 --route Farkas --proof-status checked`; `checks --pack finite-line-search-v0 --route Farkas --proof-status checked --text direction`; `checks --pack finite-wolfe-line-search-v0 --route Farkas --proof-status checked` |
| Projected and proximal gradient display rows | packs `finite-projected-gradient-v0`, `finite-proximal-gradient-v0` | `Farkas` | `checks --pack finite-projected-gradient-v0 --route Farkas --proof-status checked`; `checks --pack finite-proximal-gradient-v0 --route Farkas --proof-status checked`; `checks --pack finite-proximal-gradient-v0 --route Farkas --proof-status checked --text decrease`; `checks --pack finite-proximal-gradient-v0 --route Farkas --proof-status checked --text box` |

## Copyable Examples

List all promoted optimization and convexity packs:

```sh
python3 scripts/query-foundational-resources.py packs \
  --field optimization_and_convexity \
  --route Farkas \
  --require-any
```

Display all checked optimization and convexity Farkas rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field optimization_and_convexity \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked LP objective-threshold rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_lp_objective_farkas \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked convexity, separation, KKT, QP, SDP, and method-step rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_rational_convexity_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-separation-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text separation \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-root-finding-v0 \
  --route Farkas \
  --proof-status checked \
  --text width \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text root-finding \
  --require-any
```

Display the checked convexity threshold conflict row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack convexity-rational-v0 \
  --route Farkas \
  --proof-status checked \
  --text threshold \
  --require-any
```

Display checked projection and least-squares rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_inner_product_projection \
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
```

Display checked exact-vs-floating boundary rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_exact_vs_floating_arithmetic \
  --route Farkas \
  --proof-status checked \
  --require-any
```

For focused UI cards, query individual optimization packs:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-kkt-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text KKT \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-active-set-qp-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text active-set \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-active-set-qp-v0 \
  --route Farkas \
  --proof-status checked \
  --text inactive \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-active-set-qp-v0 \
  --route Farkas \
  --proof-status checked \
  --text degenerate \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-sdp-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-gradient-descent-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-line-search-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-line-search-v0 \
  --route Farkas \
  --proof-status checked \
  --text direction \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-wolfe-line-search-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-projected-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-proximal-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-proximal-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --text decrease \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-proximal-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --text box \
  --require-any
```

## Current Boundary

These queries prove discoverability of finite checked optimization rows, not
theorem coverage. They can support a catalog, learner page, route-specific
regression search, or sibling resource that wants examples by finite method
family.

They do not prove:

- LP or convex-program strong duality;
- KKT sufficiency or active-set method correctness;
- SDP strong duality or semidefinite optimization theory;
- root-finding convergence, error-bound, or numerical-stability theorems;
- gradient descent, line-search, Wolfe, projected-gradient, or
  proximal-gradient convergence;
- floating-point stability, conditioning, performance, or benchmark parity;
- theorem-level convex analysis or infinite-dimensional optimization claims.

Those claims need new proof-horizon rows, theorem-prover reconstruction,
numerical-analysis artifacts, or benchmark evidence before they can graduate.
