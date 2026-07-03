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
thresholds, convexity shadows, convex-analysis theorem boundaries, finite
separation, KKT stationarity and complementarity, active-set QP face/slack and
degenerate-bound replay, tiny SDP
objective/slack/gap replay, gradient-descent steps, Armijo/Wolfe line-search
rows, projected-gradient interval/decrease replay, proximal-gradient
soft-threshold and composite-decrease plus box-plus-L1 replay, Schur-complement
positive-definite shadows, least-squares
and ridge-regression rows, residual bounds, and projection witnesses. General duality, KKT
sufficiency, SDP strong duality, method
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
| Convexity, separation, KKT, QP, SDP, conjugate-gradient, and finite first-order method shadows | `bridge_rational_convexity_shadow` | `Farkas` | `checks --concept bridge_rational_convexity_shadow --route Farkas --proof-status checked` |
| Affine-threshold convexity display row | pack `convexity-rational-v0`, text `threshold` | `Farkas` | `checks --pack convexity-rational-v0 --route Farkas --proof-status checked --text threshold` |
| Convex-analysis theorem boundary | pack `convexity-rational-v0` or text `convex-analysis` | `Lean horizon` | `horizon-frontier --pack convexity-rational-v0`; `horizon-frontier --text convex-analysis` |
| Inner-product projection, least-squares, ridge, and finite discriminant rows | `bridge_inner_product_projection`; packs `finite-ridge-regression-v0`, `finite-linear-discriminant-v0` | `Farkas` | `checks --concept bridge_inner_product_projection --route Farkas --proof-status checked`; `checks --pack finite-ridge-regression-v0 --route Farkas --proof-status checked`; `checks --pack finite-linear-discriminant-v0 --route Farkas --proof-status checked` |
| Residual bounds and regression/numerical optimization rows | `bridge_residual_bound`; pack `finite-ridge-regression-v0` | `Farkas` | `checks --concept bridge_residual_bound --route Farkas --proof-status checked`; `checks --pack finite-ridge-regression-v0 --route Farkas --proof-status checked` |
| Exact arithmetic, regularized regression, finite discriminants, and numerical-honesty rows | `bridge_exact_vs_floating_arithmetic`; packs `finite-ridge-regression-v0`, `finite-linear-discriminant-v0` | `Farkas` | `checks --concept bridge_exact_vs_floating_arithmetic --route Farkas --proof-status checked`; `checks --pack finite-ridge-regression-v0 --route Farkas --proof-status checked`; `checks --pack finite-linear-discriminant-v0 --route Farkas --proof-status checked`; `horizon-frontier --text discriminant` |
| Finite linear-discriminant/classification optimization shadow | `bridge_finite_linear_discriminant_shadow`; pack `finite-linear-discriminant-v0` | `Farkas` | `checks --concept bridge_finite_linear_discriminant_shadow --route Farkas --proof-status checked`; `checks --pack finite-linear-discriminant-v0 --route Farkas --proof-status checked`; `horizon-frontier --text discriminant` |
| KKT stationarity and complementarity display rows | pack `finite-kkt-v0` | `Farkas` | `checks --pack finite-kkt-v0 --route Farkas --proof-status checked` |
| Active-set QP display row | pack `finite-active-set-qp-v0` | `Farkas` | `checks --pack finite-active-set-qp-v0 --route Farkas --proof-status checked` |
| Inactive active-set slack row | pack `finite-active-set-qp-v0`, text `inactive` | `Farkas` | `checks --pack finite-active-set-qp-v0 --route Farkas --proof-status checked --text inactive` |
| Degenerate active-set multiplier row | pack `finite-active-set-qp-v0`, text `degenerate` | `Farkas` | `checks --pack finite-active-set-qp-v0 --route Farkas --proof-status checked --text degenerate` |
| SDP objective/slack/gap display row | pack `finite-sdp-v0` | `Farkas` | `checks --pack finite-sdp-v0 --route Farkas --proof-status checked`; `checks --pack finite-sdp-v0 --route Farkas --proof-status checked --text slack` |
| Schur-complement positive-definite shadow row | `bridge_schur_complement`; pack `finite-schur-complement-v0` | `Farkas` | `checks --concept bridge_schur_complement --route Farkas --proof-status checked`; `checks --pack finite-schur-complement-v0 --route Farkas --proof-status checked` |
| Conjugate-gradient, gradient-descent, and line-search display rows | packs `finite-conjugate-gradient-v0`, `finite-gradient-descent-v0`, `finite-line-search-v0`, `finite-wolfe-line-search-v0` | `Farkas` | `checks --pack finite-conjugate-gradient-v0 --route Farkas --proof-status checked`; `checks --pack finite-gradient-descent-v0 --route Farkas --proof-status checked`; `checks --pack finite-line-search-v0 --route Farkas --proof-status checked`; `checks --pack finite-line-search-v0 --route Farkas --proof-status checked --text direction`; `checks --pack finite-wolfe-line-search-v0 --route Farkas --proof-status checked` |
| Projected and proximal gradient display rows | packs `finite-projected-gradient-v0`, `finite-proximal-gradient-v0` | `Farkas` | `checks --pack finite-projected-gradient-v0 --route Farkas --proof-status checked`; `checks --pack finite-projected-gradient-v0 --route Farkas --proof-status checked --text projection`; `checks --pack finite-projected-gradient-v0 --route Farkas --proof-status checked --text decrease`; `checks --pack finite-proximal-gradient-v0 --route Farkas --proof-status checked`; `checks --pack finite-proximal-gradient-v0 --route Farkas --proof-status checked --text decrease`; `checks --pack finite-proximal-gradient-v0 --route Farkas --proof-status checked --text box` |

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

Display the convex-analysis theorem boundary:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack convexity-rational-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text convex-analysis \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack convexity-rational-v0 \
  --proof-status lean-horizon \
  --require-any
```

Display checked projection and least-squares rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_inner_product_projection \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-ridge-regression-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_linear_discriminant_shadow \
  --pack finite-linear-discriminant-v0 \
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
  --concept bridge_residual_bound \
  --pack finite-ridge-regression-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked Schur-complement optimization-adjacent rows:

```sh
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

Display checked exact-vs-floating boundary rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_exact_vs_floating_arithmetic \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text ridge \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text discriminant \
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

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text SDP \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-gradient-descent-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-conjugate-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text gradient \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-line-search-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text line-search \
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

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "Wolfe line-search" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-projected-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text projected-gradient \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-projected-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --text projection \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-projected-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --text decrease \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-proximal-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text proximal-gradient \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-proximal-gradient-v0 \
  --route Farkas \
  --proof-status checked \
  --text proximal \
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

- Jensen inequalities, midpoint-convexity equivalences, or global convexity
  criteria;
- LP or convex-program strong duality;
- KKT sufficiency or active-set method correctness;
- SDP strong duality or semidefinite optimization theory;
- root-finding convergence, error-bound, or numerical-stability theorems;
- gradient descent, line-search, Wolfe, projected-gradient, or
  proximal-gradient convergence;
- general ridge-regression optimality, regularization paths, model-selection,
  cross-validation, or statistical guarantees;
- Fisher LDA optimality, Gaussian classifier assumptions, multiclass
  discriminants, statistical classifier guarantees, or floating-point
  classifier implementations;
- floating-point stability, conditioning, performance, or benchmark parity;
- theorem-level convex analysis or infinite-dimensional optimization claims.

Those claims need new proof-horizon rows, theorem-prover reconstruction,
numerical-analysis artifacts, or benchmark evidence before they can graduate.
