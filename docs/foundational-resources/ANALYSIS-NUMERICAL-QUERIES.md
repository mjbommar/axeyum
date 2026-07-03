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

The current surface is finite and exact-rational: metric balls, rational
interval arithmetic, bounded
epsilon-delta shadows, bounded sequence tails, algebraic derivative and
integral replay, Newton/root-finding steps, finite recurrence, Euler,
Runge-Kutta midpoint, Heun, backward Euler, Crank-Nicolson,
Adams-Bashforth, BDF2, Simpson-rule quadrature, Romberg extrapolation,
finite-difference derivative
stencils, finite Taylor polynomial rows, cubic Hermite interpolation rows,
natural cubic spline assembly rows, and divided-difference interpolation rows,
residual/solution-box/Jacobi rows, exact condition-number, Schur-complement,
singular-value shadows, regularized normal-equation and linear-discriminant replay, fixed-decimal rounding shadows,
exact-vs-floating boundary rows, complex numbers as real-pair algebra, and one
finite Cauchy-Riemann partial-derivative shadow. Polynomial rows are fixed
coefficient, factor, root, discriminant, derivative, component-partial, and
coefficient-window or interpolation-table checks, not general analytic theory. Completeness,
IVT/MVT/FTC, uniform convergence, analytic continuation, holomorphicity,
contour integration, general factorization, algebraic closure, numerical
stability, and floating-point error guarantees remain in the proof-horizon or
numerical-honesty lanes.
For the focused learner-facing boundary over exact complex real-pair,
complex-plane transform, finite Cauchy-Riemann shadow, fixed root, and
rational-polynomial factorization resources, read
[Complex Analysis Theorem Boundary](../learn/math/complex-analysis-theorem-boundary.md).
For the focused calculus boundary over finite derivative, finite-difference
stencils, finite Riemann-sum, finite Simpson-rule quadrature, finite Romberg
extrapolation, gradient, Jacobian, Hessian, and malformed-row shadows, read
[Calculus Theorem Boundary](../learn/math/calculus-theorem-boundary.md).
For the focused convex-analysis boundary over finite midpoint, grid,
threshold, and malformed-row shadows, read
[Convexity Theorem Boundary](../learn/math/convexity-theorem-boundary.md).

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
| Rational intervals and exact real-analysis bounds | `bridge_rational_interval_replay`; pack `finite-interval-arithmetic-shadow-v0` | `Farkas` | `concepts --field real_analysis --text "Rational Interval"`; `checks --pack finite-interval-arithmetic-shadow-v0 --route Farkas --proof-status checked` |
| Sequence tails, Cauchy shadows, and squeeze side conditions | `bridge_sequence_tail_shadow`; `bridge_cauchy_tail_shadow`; `bridge_squeeze_shadow` | `Farkas`; finite replay | `concepts --field real_analysis --text "Sequence Tail"`; `concepts --field real_analysis --text "Cauchy Tail"`; `concepts --field real_analysis --text "Squeeze Shadow"` |
| Sequence and fixed-point acceleration shadows | packs `finite-aitken-acceleration-v0`, `finite-steffensen-method-v0`; concepts `bridge_sequence_tail_shadow`, `bridge_bounded_family_asymptotic_boundary`, `bridge_exact_vs_floating_arithmetic` | `Farkas`; Lean horizon | `checks --pack finite-aitken-acceleration-v0 --route Farkas --proof-status checked`; `checks --pack finite-steffensen-method-v0 --route Farkas --proof-status checked`; `horizon-frontier --text Steffensen` |
| Derivative identities and integration horizons | `bridge_derivative_identity_shadow`; `bridge_integration_horizon` | `Farkas`; Lean horizon | `concepts --field real_analysis --text "Derivative Identity"`; `concepts --field real_analysis --text "Integration Horizon"` |
| Metric balls and bounded epsilon-delta rows | `bridge_metric_ball`; `bridge_bounded_epsilon_delta_shadow` | `Farkas` | `checks --concept bridge_bounded_epsilon_delta_shadow --route Farkas --proof-status checked` |
| Algebraic derivative, finite-difference, Taylor-polynomial, Hermite interpolation, natural spline assembly, Riemann-sum, Simpson-rule, Romberg extrapolation, and multivariable calculus shadows | packs `calculus-algebraic-shadow-v0`, `finite-difference-derivatives-v0`, `finite-taylor-polynomials-v0`, `finite-cubic-hermite-interpolation-v0`, `finite-cubic-spline-interpolation-v0`, `calculus-riemann-sum-v0`, `finite-simpson-rule-v0`, `finite-romberg-extrapolation-v0`, `multivariable-calculus-rational-v0` | `Farkas`; Lean horizon | `checks --pack calculus-algebraic-shadow-v0 --route Farkas --proof-status checked`; `checks --pack finite-difference-derivatives-v0 --route Farkas --proof-status checked`; `checks --pack finite-taylor-polynomials-v0 --route Farkas --proof-status checked`; `checks --pack finite-cubic-hermite-interpolation-v0 --route Farkas --proof-status checked`; `checks --pack finite-cubic-spline-interpolation-v0 --route Farkas --proof-status checked`; `checks --pack calculus-riemann-sum-v0 --route Farkas --proof-status checked`; `checks --pack finite-simpson-rule-v0 --route Farkas --proof-status checked`; `checks --pack finite-romberg-extrapolation-v0 --route Farkas --proof-status checked`; `horizon-frontier --text calculus` |
| Exact finite convexity and convex-analysis horizons | pack `convexity-rational-v0`; concept `bridge_rational_convexity_shadow` | `Farkas`; Lean horizon | `checks --pack convexity-rational-v0 --route Farkas --proof-status checked`; `horizon-frontier --text convex-analysis` |
| Polynomial coefficients, factors, roots, coefficient windows, divided-difference interpolation, barycentric interpolation, Taylor-polynomial replay, Hermite interpolation, and natural spline assembly | `bridge_polynomial_coefficient_factor_replay`; packs `finite-divided-differences-v0`, `finite-barycentric-interpolation-v0`, `finite-taylor-polynomials-v0`, `finite-cubic-hermite-interpolation-v0`, `finite-cubic-spline-interpolation-v0` | `Diophantine`; `Farkas` | `checks --concept bridge_polynomial_coefficient_factor_replay --route Diophantine --proof-status checked`; `checks --concept bridge_polynomial_coefficient_factor_replay --route Farkas --proof-status checked`; `checks --pack finite-divided-differences-v0 --route Farkas --proof-status checked`; `checks --pack finite-barycentric-interpolation-v0 --route Farkas --proof-status checked`; `checks --pack finite-taylor-polynomials-v0 --route Farkas --proof-status checked`; `checks --pack finite-cubic-hermite-interpolation-v0 --route Farkas --proof-status checked`; `checks --pack finite-cubic-spline-interpolation-v0 --route Farkas --proof-status checked` |
| Root-finding, secant-method, and Newton-step rows | packs `finite-root-finding-v0`, `finite-secant-method-v0`; concept `bridge_exact_vs_floating_arithmetic` | `Farkas` | `checks --pack finite-root-finding-v0 --route Farkas --proof-status checked`; `checks --pack finite-secant-method-v0 --route Farkas --proof-status checked` |
| Finite dynamics, recurrence, Euler, Runge-Kutta midpoint, Heun, Backward Euler, Crank-Nicolson, Adams-Bashforth, and BDF2 replay | `bridge_finite_dynamics_euler_replay` | `Farkas` | `checks --concept bridge_finite_dynamics_euler_replay --route Farkas --proof-status checked`; `checks --pack finite-runge-kutta-midpoint-v0 --route Farkas --proof-status checked`; `checks --pack finite-heun-method-v0 --route Farkas --proof-status checked`; `checks --pack finite-backward-euler-method-v0 --route Farkas --proof-status checked`; `checks --pack finite-crank-nicolson-method-v0 --route Farkas --proof-status checked`; `checks --pack finite-adams-bashforth-method-v0 --route Farkas --proof-status checked`; `checks --pack finite-bdf2-method-v0 --route Farkas --proof-status checked` |
| Residuals, solution boxes, Jacobi steps, condition numbers, GMRES residual minimization, ridge normal equations, finite discriminants, Schur complements, real Schur decomposition, polar decomposition, QR iteration and shifted-QR steps, singular values, and exact matrix factorizations | `bridge_residual_bound`; `bridge_lu_replay`; `bridge_schur_complement`; `bridge_finite_linear_discriminant_shadow`; pack `finite-ridge-regression-v0`; pack `finite-linear-discriminant-v0`; pack `finite-gmres-residual-shadow-v0`; pack `finite-singular-value-shadow-v0`; pack `finite-real-schur-decomposition-v0`; pack `finite-polar-decomposition-v0`; pack `finite-qr-iteration-step-v0`; pack `finite-shifted-qr-step-v0` | `Farkas` | `checks --concept bridge_residual_bound --route Farkas --proof-status checked`; `checks --pack finite-ridge-regression-v0 --route Farkas --proof-status checked`; `checks --pack finite-linear-discriminant-v0 --route Farkas --proof-status checked`; `checks --concept bridge_finite_linear_discriminant_shadow --route Farkas --proof-status checked`; `checks --concept bridge_schur_complement --route Farkas --proof-status checked`; `checks --pack numerical-linear-algebra-v0 --route Farkas --proof-status checked`; `checks --pack finite-condition-number-v0 --route Farkas --proof-status checked`; `checks --pack finite-gmres-residual-shadow-v0 --route Farkas --proof-status checked`; `checks --pack finite-schur-complement-v0 --route Farkas --proof-status checked`; `checks --pack finite-real-schur-decomposition-v0 --route Farkas --proof-status checked`; `checks --pack finite-polar-decomposition-v0 --route Farkas --proof-status checked`; `checks --pack finite-qr-iteration-step-v0 --route Farkas --proof-status checked`; `checks --pack finite-shifted-qr-step-v0 --route Farkas --proof-status checked`; `checks --pack finite-singular-value-shadow-v0 --route Farkas --proof-status checked`; `checks --pack numerical-linear-algebra-v0 --route Farkas --proof-status checked --text solution`; `checks --pack finite-lu-decomposition-v0 --route Farkas --proof-status checked`; `checks --pack finite-pivoted-lu-decomposition-v0 --route Farkas --proof-status checked`; `checks --pack finite-ldlt-decomposition-v0 --route Farkas --proof-status checked`; `checks --pack finite-cholesky-decomposition-v0 --route Farkas --proof-status checked` |
| Operator/Chebyshev, spectral, orthogonal-diagonalization, GMRES, real-Schur, polar, QR-step, shifted-QR, and singular-value numerical rows | `bridge_finite_operator_chebyshev`; `bridge_eigenpair` | `Farkas` | `checks --concept bridge_finite_operator_chebyshev --route Farkas --proof-status checked`; `checks --concept bridge_eigenpair --route Farkas --proof-status checked`; `checks --pack finite-gmres-residual-shadow-v0 --route Farkas --proof-status checked`; `checks --pack finite-orthogonal-diagonalization-v0 --route Farkas --proof-status checked`; `checks --pack finite-real-schur-decomposition-v0 --route Farkas --proof-status checked`; `checks --pack finite-polar-decomposition-v0 --route Farkas --proof-status checked`; `checks --pack finite-qr-iteration-step-v0 --route Farkas --proof-status checked`; `checks --pack finite-shifted-qr-step-v0 --route Farkas --proof-status checked`; `checks --pack finite-singular-value-shadow-v0 --route Farkas --proof-status checked` |
| Complex numbers, plane transforms, and Cauchy-Riemann shadows as real-pair algebra | `bridge_complex_real_pair_transform`; pack `finite-cauchy-riemann-shadow-v0` | `Farkas` | `checks --concept bridge_complex_real_pair_transform --route Farkas --proof-status checked`; `checks --pack finite-cauchy-riemann-shadow-v0 --route Farkas --proof-status checked` |
| Exact-vs-floating boundary rows | `bridge_exact_vs_floating_arithmetic`; packs `finite-rounding-shadow-v0`, `finite-interval-arithmetic-shadow-v0`, `finite-romberg-extrapolation-v0`, `finite-secant-method-v0`, `finite-aitken-acceleration-v0`, `finite-steffensen-method-v0`, `finite-ridge-regression-v0`, `finite-linear-discriminant-v0` | `Farkas` | `checks --concept bridge_exact_vs_floating_arithmetic --route Farkas --proof-status checked`; `checks --pack finite-rounding-shadow-v0 --route Farkas --proof-status checked`; `checks --pack finite-interval-arithmetic-shadow-v0 --route Farkas --proof-status checked`; `checks --pack finite-romberg-extrapolation-v0 --route Farkas --proof-status checked`; `checks --pack finite-secant-method-v0 --route Farkas --proof-status checked`; `checks --pack finite-aitken-acceleration-v0 --route Farkas --proof-status checked`; `checks --pack finite-steffensen-method-v0 --route Farkas --proof-status checked`; `checks --pack finite-ridge-regression-v0 --route Farkas --proof-status checked`; `checks --pack finite-linear-discriminant-v0 --route Farkas --proof-status checked` |

## Copyable Examples

Display checked bounded epsilon-delta and finite sequence-tail rows:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field real_analysis \
  --text "Rational Interval" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-interval-arithmetic-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field real_analysis \
  --text "Sequence Tail" \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field real_analysis \
  --text "Cauchy Tail" \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field real_analysis \
  --text "Squeeze Shadow" \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field real_analysis \
  --text "Derivative Identity" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-cauchy-riemann-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field real_analysis \
  --text "Integration Horizon" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_bounded_epsilon_delta_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display the checked finite recurrence-prefix affine-step proof row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-recurrence-prefix-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-affine-step \
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
python3 scripts/query-foundational-resources.py concepts \
  --field real_analysis \
  --text polynomial \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_polynomial_coefficient_factor_replay \
  --route Diophantine \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_polynomial_coefficient_factor_replay \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-divided-differences-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-interpolation-value \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_polynomial_coefficient_factor_replay \
  --pack finite-divided-differences-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-barycentric-interpolation-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-barycentric-value \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_polynomial_coefficient_factor_replay \
  --pack finite-barycentric-interpolation-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-difference-derivatives-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-finite-difference-value \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_derivative_identity_shadow \
  --pack finite-difference-derivatives-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-taylor-polynomials-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-taylor-value \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_derivative_identity_shadow \
  --pack finite-taylor-polynomials-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_polynomial_coefficient_factor_replay \
  --pack finite-taylor-polynomials-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-cubic-hermite-interpolation-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-hermite-value \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_derivative_identity_shadow \
  --pack finite-cubic-hermite-interpolation-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_polynomial_coefficient_factor_replay \
  --pack finite-cubic-hermite-interpolation-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-cubic-spline-interpolation-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-spline-value \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_derivative_identity_shadow \
  --pack finite-cubic-spline-interpolation-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_polynomial_coefficient_factor_replay \
  --pack finite-cubic-spline-interpolation-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

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
  --pack finite-simpson-rule-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_integration_horizon \
  --pack finite-simpson-rule-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-romberg-extrapolation-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-romberg-value \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_integration_horizon \
  --pack finite-romberg-extrapolation-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack multivariable-calculus-rational-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text calculus \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack convexity-rational-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text convex-analysis \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-aitken-acceleration-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-aitken-value \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text Aitken \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-steffensen-method-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-steffensen-value \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text Steffensen \
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

python3 scripts/query-foundational-resources.py checks \
  --pack finite-secant-method-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-secant-step \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text secant \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text root-finding \
  --require-any
```

Display checked finite dynamics, recurrence, and Euler rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_dynamics_euler_replay \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text recurrence \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text ODE \
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
  --concept bridge_schur_complement \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-schur-complement-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-orthogonal-diagonalization-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-real-schur-decomposition-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-polar-decomposition-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-qr-iteration-step-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-shifted-qr-step-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-singular-value-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-pivoted-lu-decomposition-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-ldlt-decomposition-v0 \
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

Display complex-analysis and factorization theorem horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --field complex_analysis \
  --shadow-state checked-finite-shadow \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack complex-plane-transforms-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack polynomial-factorization-rational-v0 \
  --require-any
```

Display checked exact-vs-floating boundary rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_exact_vs_floating_arithmetic \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-rounding-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-interval-arithmetic-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-steffensen-method-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-ridge-regression-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-linear-discriminant-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-singular-value-shadow-v0 \
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
  --pack sequence-limit-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --text reciprocal \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack bounded-monotone-sequence-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-upper-bound \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack bounded-monotone-sequence-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-tail-gap \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text monotone \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-euler-method-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-heun-method-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-backward-euler-method-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-crank-nicolson-method-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-adams-bashforth-method-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-bdf2-method-v0 \
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

For the finite ODE time-stepping boundary, read
[Euler Method Theorem Boundary](../learn/math/euler-method-theorem-boundary.md)
before displaying ODE convergence, stability, stiffness, PDE, or
floating-point method claims next to exact rational finite-step rows.

For the finite calculus boundary, read
[Calculus Theorem Boundary](../learn/math/calculus-theorem-boundary.md)
before displaying differentiability, MVT, integrability, FTC,
inverse/implicit-function, change-of-variables, or manifold-calculus claims
next to exact polynomial derivative, finite-sum, gradient, Jacobian, Hessian,
or bad-row examples.

For the complex-analysis boundary, read
[Complex Analysis Theorem Boundary](../learn/math/complex-analysis-theorem-boundary.md)
before displaying holomorphic, contour-integral, analytic-continuation,
algebraic-closure, or arbitrary factorization claims next to exact real-pair
and coefficient rows.

For the bounded monotone sequence boundary, read
[Monotone Convergence Theorem Boundary](../learn/math/monotone-convergence-theorem-boundary.md)
before displaying general monotone convergence, supremum, or real-completeness
claims next to exact rational finite-prefix and finite-tail rows.

For the finite recurrence/asymptotic boundary, read
[Recurrence And Asymptotic Theorem Boundary](../learn/math/recurrence-asymptotic-theorem-boundary.md)
before displaying induction-over-all-`n`, closed-form, asymptotic-growth,
convergence, stability, or big-O language next to finite recurrence prefixes,
companion-matrix traces, or finite cost counters.

They do not prove:

- completeness, IVT/MVT/FTC, compactness, or arbitrary convergence theorems;
- theorem-level epsilon-delta calculus beyond the finite bounded rows;
- numerical stability, conditioning, floating-point error bounds, or
  performance claims;
- general Fisher LDA optimality, classifier generalization, or floating-point
  classifier implementations;
- holomorphicity, Cauchy theory, residues, contour integration, analytic
  continuation, or algebraic closure;
- benchmark performance, PAR-2, or Z3/cvc5 parity.

Those claims need new proof-horizon rows, theorem-prover reconstruction,
numerical-analysis artifacts, or benchmark evidence before they can graduate.
