# End To End: Finite Conjugate Gradient

This lesson follows one exact finite conjugate-gradient resource from an
initial residual through two CG steps, residual orthogonality, A-conjugacy,
exact solution replay, and a checked bad-step-size rejection. It uses the
[finite-conjugate-gradient-v0](../../../artifacts/examples/math/finite-conjugate-gradient-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and
  `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_linear_algebra`, `field_numerical_analysis`, and
  `field_optimization_and_convexity` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_residual_bound`, `bridge_rational_convexity_shadow`, and
  `bridge_exact_vs_floating_arithmetic` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `initial-residual-replay` | `sat` | replay-only |
| `first-cg-step-replay` | `sat` | replay-only |
| `residual-orthogonality-replay` | `sat` | replay-only |
| `beta-direction-replay` | `sat` | replay-only |
| `search-direction-conjugacy-replay` | `sat` | replay-only |
| `second-step-solution-replay` | `sat` | replay-only |
| `bad-cg-alpha0-rejected` | `unsat` | replay-only |
| `qf-lra-bad-cg-alpha0` | `unsat` | checked |
| `general-conjugate-gradient-theory-lean-horizon` | `not-run` | Lean horizon |

The pack uses one rational SPD matrix:

```text
A = [[4, 1],
     [1, 3]]
b = [1, 2]
x0 = [0, 0]
```

## Replay The Initial Residual

The initial residual is:

```text
r0 = b - A*x0 = [1,2]
p0 = r0
```

The validator recomputes the matrix-vector product and residual exactly.

## Replay The First CG Step

The first matrix-vector product and dot products are:

```text
A*p0 = [6,7]
r0^T*r0 = 5
p0^T*A*p0 = 20
```

So the exact first step size is:

```text
alpha0 = 5/20 = 1/4
```

The first update is:

```text
x1 = x0 + alpha0*p0 = [1/4,1/2]
r1 = r0 - alpha0*A*p0 = [-1/2,1/4]
```

## Replay Orthogonality And Conjugacy

The new residual is orthogonal to the old search direction:

```text
r1^T*p0 = (-1/2)*1 + (1/4)*2 = 0
```

The Fletcher-Reeves update is:

```text
r1^T*r1 = 5/16
beta0 = (5/16)/5 = 1/16
p1 = r1 + beta0*p0 = [-7/16,3/8]
```

The directions are A-conjugate:

```text
A*p1 = [-11/8, 11/16]
p0^T*A*p1 = 0
```

This is exact finite replay of the CG algebra, not a proof of the general
Krylov minimization theorem.

## Replay The Second Step

The second denominator is:

```text
p1^T*A*p1 = 55/64
```

So:

```text
alpha1 = (5/16) / (55/64) = 4/11
x2 = x1 + alpha1*p1 = [1/11,7/11]
```

The validator checks:

```text
A*x2 - b = [0,0]
```

So this fixed two-dimensional exact instance reaches the exact solution in two
steps.

## Reject A Bad Step Size

The bad source row claims:

```text
alpha0 = 1/3
```

Exact replay computes:

```text
alpha0 = 1/4
```

The checked `QF_LRA` artifact isolates the scalar contradiction:

```text
cg_alpha0 = 1/4
cg_alpha0 = 1/3
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass independent
certificate checking.

## Name The Horizon

This pack does not claim:

```text
general CG convergence
finite termination for arbitrary n-dimensional SPD systems
Krylov minimization theorem
preconditioner correctness
roundoff behavior
floating-point CG stability
```

Those require Lean theorem statements, proof-producing linear-algebra
certificates, or separate numerical-honesty artifacts.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-conjugate-gradient-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_conjugate_gradient_bad_alpha0_artifact_emits_checked_farkas
```

Expected output from the pack validator:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate CG transcript, residuals, directions, steps
trusted small checking -> exact rational matrix-vector and dot-product replay
proof upgrade -> QF_LRA/Farkas certificate for the false step-size claim
remaining horizon -> CG theory, preconditioning, roundoff, and stability proofs
```

The graduation route is deterministic exact-rational finite-matrix checking
plus checked proof objects for false finite claims before broader CG or
floating-point solver claims are promoted.
