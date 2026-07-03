# End To End: Finite GMRES Residual Shadow

This lesson follows one exact finite GMRES resource from an initial residual to
a one-dimensional Krylov direction, an exact residual-minimizing coefficient,
residual orthogonality, residual decrease, and a checked bad-alpha rejection.
It uses the
[finite-gmres-residual-shadow-v0](../../../artifacts/examples/math/finite-gmres-residual-shadow-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra` and `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_linear_algebra`, `field_numerical_analysis`,
  `field_functional_analysis_and_operator_theory`, and
  `field_optimization_and_convexity` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_residual_bound`, `bridge_finite_operator_chebyshev`, and
  `bridge_inner_product_projection` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `initial-residual-witness` | `sat` | replay-only |
| `krylov-direction-witness` | `sat` | replay-only |
| `one-step-gmres-minimizer-witness` | `sat` | replay-only |
| `residual-orthogonality-witness` | `sat` | replay-only |
| `residual-improvement-witness` | `sat` | replay-only |
| `bad-gmres-alpha-rejected` | `unsat` | replay-only |
| `qf-lra-bad-gmres-alpha` | `unsat` | checked |
| `general-gmres-theory-lean-horizon` | `not-run` | Lean horizon |

The pack uses one rational matrix, one right-hand side, and the zero initial
point:

```text
A = [[2, 1],
     [1, 2]]
b  = [1, 0]
x0 = [0, 0]
```

## Replay The Initial Residual

The initial residual is:

```text
r0 = b - A*x0 = [1,0]
r0^T*r0 = 1
```

The validator recomputes the matrix-vector product and dot product exactly.

## Replay The Krylov Direction

The one-step Krylov basis vector is `r0`, so the search image is:

```text
A*r0 = [2,1]
(A*r0)^T*(A*r0) = 5
r0^T*(A*r0) = 2
```

This is exact rational replay, not a floating-point Arnoldi or least-squares
routine.

## Replay The One-Step Minimizer

One-step GMRES minimizes:

```text
||b - alpha*A*r0||_2^2
```

For this fixed row, the exact minimizer coefficient is:

```text
alpha = (r0^T A r0) / ((A r0)^T(A r0)) = 2/5
```

The updated approximation and residual are:

```text
x1 = x0 + alpha*r0 = [2/5,0]
A*x1 = [4/5,2/5]
r1 = b - A*x1 = [1/5,-2/5]
```

## Replay Orthogonality And Decrease

The residual is orthogonal to the Krylov image:

```text
r1^T*(A*r0) = (1/5)*2 + (-2/5)*1 = 0
```

The residual norm decreases exactly:

```text
||r0||_2^2 = 1
||r1||_2^2 = 1/5
decrease = 4/5
```

The pack checks the finite arithmetic only. It does not infer a convergence
rate or a property of arbitrary systems.

## Reject A Bad Alpha

The bad source row claims:

```text
alpha = 1/2
```

Exact replay computes:

```text
alpha = 2/5
```

The checked `QF_LRA` artifact isolates the scalar contradiction:

```text
gmres_alpha = 2/5
gmres_alpha = 1/2
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass independent
certificate checking.

## Name The Horizon

This pack does not claim:

```text
general k-step GMRES residual-minimization theorem
Arnoldi least-squares theorem for arbitrary systems
restart policy correctness
preconditioner correctness
breakdown behavior
nonnormal convergence theory
floating-point Krylov stability
```

Those require Lean theorem statements, proof-producing linear-algebra
certificates, or separate numerical-honesty artifacts.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-gmres-residual-shadow-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_gmres_residual_shadow_bad_alpha_artifact_emits_checked_farkas
```

Expected output from the pack validator:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate GMRES coefficient, residual, and norm data
trusted small checking -> exact rational matrix-vector products and dot products
proof upgrade -> QF_LRA/Farkas certificate for the false alpha claim
remaining horizon -> GMRES theory, restarts, preconditioning, breakdown, and stability
```

The graduation route is deterministic exact-rational finite-matrix checking
plus checked proof objects for false finite claims before broader GMRES or
floating-point solver claims are promoted.
