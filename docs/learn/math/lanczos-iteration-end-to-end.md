# End To End: Finite Lanczos Iteration

This lesson follows one exact finite Lanczos resource from a normalized start
vector to an orthonormal Krylov basis, a symmetric tridiagonal matrix, the
finite relation `A*Q = Q*T`, and a checked bad-coefficient rejection. It uses
the
[finite-lanczos-iteration-v0](../../../artifacts/examples/math/finite-lanczos-iteration-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra` and `curriculum_rationals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_linear_algebra`, `field_numerical_analysis`, and
  `field_functional_analysis_and_operator_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_residual_bound`, `bridge_eigenpair`,
  `bridge_inner_product_projection`, and
  `bridge_exact_vs_floating_arithmetic` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `initial-lanczos-vector-replay` | `sat` | replay-only |
| `first-lanczos-step-replay` | `sat` | replay-only |
| `lanczos-orthonormal-basis-replay` | `sat` | replay-only |
| `second-lanczos-step-replay` | `sat` | replay-only |
| `tridiagonal-relation-replay` | `sat` | replay-only |
| `bad-lanczos-beta1-rejected` | `unsat` | replay-only |
| `qf-lra-bad-lanczos-beta1` | `unsat` | checked |
| `general-lanczos-theory-lean-horizon` | `not-run` | Lean horizon |

The pack uses one symmetric rational matrix and one starting vector:

```text
A = [[2, 1],
     [1, 2]]
q1 = [1, 0]
```

## Replay The First Step

The starting vector is normalized:

```text
q1^T*q1 = 1
```

The first matrix-vector product is:

```text
A*q1 = [2,1]
```

The first Lanczos coefficient is:

```text
alpha1 = q1^T*A*q1 = 2
```

Subtracting that projection leaves:

```text
v = A*q1 - alpha1*q1 = [0,1]
v^T*v = 1
beta1 = 1
q2 = v / beta1 = [0,1]
```

This is exact rational replay. There is no tolerance and no floating-point
normalization step.

## Replay Orthonormality

The validator checks:

```text
q1^T*q1 = 1
q2^T*q2 = 1
q1^T*q2 = 0
```

The symmetry of `A` is also checked because Lanczos is the symmetric-matrix
specialization of the Arnoldi story.

## Replay The Tridiagonal Relation

The second matrix-vector product is:

```text
A*q2 = [1,2]
alpha2 = q2^T*A*q2 = 2
```

The three-term residual is:

```text
A*q2 - beta1*q1 - alpha2*q2 = [0,0]
beta2 = 0
```

So the tridiagonal matrix for this full two-dimensional basis is:

```text
T = [[2, 1],
     [1, 2]]
```

With:

```text
Q = [[1, 0],
     [0, 1]]
```

the finite relation is:

```text
A*Q = Q*T
```

The validator recomputes both sides exactly.

## Reject A Bad Off-Diagonal Coefficient

The bad source row claims:

```text
beta1 = 2
```

Exact replay computes:

```text
beta1 = 1
```

The checked `QF_LRA` artifact isolates the scalar contradiction:

```text
lanczos_beta1 = 1
lanczos_beta1 = 2
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass independent
certificate checking.

## Name The Horizon

This pack does not claim:

```text
general Lanczos tridiagonalization theorem
Ritz value convergence
breakdown or restart policy correctness
finite-precision loss-of-orthogonality bounds
floating-point Krylov stability
```

Those require Lean theorem statements, proof-producing linear-algebra
certificates, or separate numerical-honesty artifacts.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-lanczos-iteration-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_lanczos_iteration_bad_beta1_artifact_emits_checked_farkas
```

Expected output from the pack validator:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate Lanczos basis and tridiagonal coefficients
trusted small checking -> exact rational dot products and matrix products
proof upgrade -> QF_LRA/Farkas certificate for the false beta1 claim
remaining horizon -> Lanczos theory, Ritz convergence, breakdown/restarts, and stability
```

The graduation route is deterministic exact-rational finite-matrix checking
plus checked proof objects for false finite claims before broader Krylov or
floating-point solver claims are promoted.
