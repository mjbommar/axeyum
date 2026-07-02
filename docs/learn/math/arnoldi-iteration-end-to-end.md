# End To End: Finite Arnoldi Iteration

This lesson follows one exact finite Arnoldi resource from a starting vector to
an orthonormal Krylov basis, a Hessenberg matrix, the finite relation
`A*Q = Q*H`, and a checked bad-coefficient rejection. It uses the
[finite-arnoldi-iteration-v0](../../../artifacts/examples/math/finite-arnoldi-iteration-v0/)
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
| `initial-krylov-vector-replay` | `sat` | replay-only |
| `first-arnoldi-projection-replay` | `sat` | replay-only |
| `arnoldi-orthonormal-basis-replay` | `sat` | replay-only |
| `second-column-hessenberg-replay` | `sat` | replay-only |
| `hessenberg-relation-replay` | `sat` | replay-only |
| `bad-arnoldi-h21-rejected` | `unsat` | replay-only |
| `qf-lra-bad-arnoldi-h21` | `unsat` | checked |
| `general-arnoldi-gmres-theory-lean-horizon` | `not-run` | Lean horizon |

The pack uses one rational matrix and one starting vector:

```text
A = [[1, 2],
     [3, 4]]
q1 = [1, 0]
```

## Replay The First Krylov Vector

The starting vector is already normalized:

```text
q1^T*q1 = 1
```

The first matrix-vector product is:

```text
A*q1 = [1,3]
```

## Replay The First Projection

The first Arnoldi coefficient is the projection back onto `q1`:

```text
h11 = q1^T*A*q1 = 1
```

Subtracting that projection leaves:

```text
v = A*q1 - h11*q1 = [0,3]
v^T*v = 9
h21 = 3
q2 = v / h21 = [0,1]
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

That is the finite table-sized part of the Arnoldi story: the basis vectors
listed in the pack really are orthonormal for this exact example.

## Replay The Hessenberg Relation

The second matrix-vector product is:

```text
A*q2 = [2,4]
h12 = q1^T*A*q2 = 2
h22 = q2^T*A*q2 = 4
```

So the Hessenberg matrix for this full two-dimensional basis is:

```text
H = [[1, 2],
     [3, 4]]
```

With:

```text
Q = [[1, 0],
     [0, 1]]
```

the finite relation is:

```text
A*Q = Q*H
```

The validator recomputes both sides exactly.

## Reject A Bad Subdiagonal Coefficient

The bad source row claims:

```text
h21 = 2
```

Exact replay computes:

```text
h21 = 3
```

The checked `QF_LRA` artifact isolates the scalar contradiction:

```text
arnoldi_h21 = 3
arnoldi_h21 = 2
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass independent
certificate checking.

## Name The Horizon

This pack does not claim:

```text
general Arnoldi decomposition theorem
Ritz value convergence
GMRES residual minimization for arbitrary systems
restart policy correctness
reorthogonalization correctness
loss-of-orthogonality bounds
floating-point Krylov stability
```

Those require Lean theorem statements, proof-producing linear-algebra
certificates, or separate numerical-honesty artifacts.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-arnoldi-iteration-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_arnoldi_iteration_bad_h21_artifact_emits_checked_farkas
```

Expected output from the pack validator:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate Arnoldi basis and Hessenberg coefficients
trusted small checking -> exact rational dot products and matrix products
proof upgrade -> QF_LRA/Farkas certificate for the false h21 claim
remaining horizon -> Arnoldi/GMRES theory, restarts, Ritz convergence, and stability
```

The graduation route is deterministic exact-rational finite-matrix checking
plus checked proof objects for false finite claims before broader Krylov or
floating-point solver claims are promoted.
