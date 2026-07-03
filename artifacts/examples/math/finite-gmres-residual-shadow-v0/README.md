# Finite GMRES Residual Shadow Checks

This pack records one exact rational one-step GMRES transcript for a fixed
two-by-two linear system. It is a small Krylov-subspace resource for linear
algebra, numerical analysis, optimization, and finite-dimensional operator
learners: replay the initial residual, form the one-dimensional Krylov
direction, compute the exact residual-minimizing coefficient, and reject one
malformed coefficient with checked QF_LRA/Farkas evidence.

The fixed system is:

```text
A = [[2, 1],
     [1, 2]]

b  = [1, 0]
x0 = [0, 0]
```

The initial residual is `r0 = b`, and the one-dimensional Krylov direction is:

```text
A*r0 = [2, 1]
```

One-step GMRES minimizes:

```text
||b - alpha*A*r0||_2^2
```

Exact replay computes:

```text
alpha = (b^T A r0) / ((A r0)^T(A r0)) = 2/5
x1    = alpha*r0 = [2/5, 0]
r1    = b - A*x1 = [1/5, -2/5]
||r1||_2^2 = 1/5
```

The checked bad row rejects the claim that the minimizer coefficient is
`alpha = 1/2`. The QF_LRA artifact isolates only the scalar contradiction:

```text
gmres_alpha = 2/5
gmres_alpha = 1/2
```

## Concept Rows

- `curriculum_linear_algebra`
- `curriculum_reals`
- `field_linear_algebra`
- `field_numerical_analysis`
- `field_functional_analysis_and_operator_theory`
- `field_optimization_and_convexity`
- `bridge_residual_bound`
- `bridge_finite_operator_chebyshev`
- `bridge_inner_product_projection`

## Trust Boundary

```text
untrusted fast search -> candidate Krylov coefficient, residual, and norm data
trusted small checking -> exact rational matrix-vector products, dot products, and checked Farkas evidence
theorem horizon       -> general GMRES least-squares theory, restart/preconditioner behavior, and floating-point stability
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-gmres-residual-shadow-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_gmres_residual_shadow_bad_alpha_artifact_emits_checked_farkas
```

Learner walkthrough:
[End To End: Finite GMRES Residual Shadow](../../../docs/learn/math/gmres-residual-shadow-end-to-end.md).
