# End To End: Finite Givens Rotation

This lesson follows one exact finite Givens rotation resource from rational
cosine/sine coefficients to an orthogonal rotation matrix, a zeroed vector, an
inverse reconstruction, and a checked bad-coefficient rejection. It uses the
[finite-givens-rotation-v0](../../../artifacts/examples/math/finite-givens-rotation-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and `curriculum_reals`
  in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_linear_algebra`, `field_numerical_analysis`,
  `field_functional_analysis_and_operator_theory`, and
  `field_optimization_and_convexity` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_lu_replay`, `bridge_inner_product_projection`, and
  `bridge_exact_vs_floating_arithmetic` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `givens-orthogonality-witness` | `sat` | replay-only |
| `givens-zeroing-witness` | `sat` | replay-only |
| `givens-inverse-reconstruction-witness` | `sat` | replay-only |
| `givens-determinant-witness` | `sat` | replay-only |
| `bad-givens-sine-rejected` | `unsat` | replay-only |
| `qf-lra-bad-givens-sine` | `unsat` | checked |
| `general-givens-qr-theory-lean-horizon` | `not-run` | Lean horizon |

The pack uses exact rational coefficients:

```text
c = 3/5
s = 4/5
```

and the rotation:

```text
G = [[ 3/5, 4/5],
     [-4/5, 3/5]]
```

## Replay Orthogonality

The validator checks:

```text
G^T*G = I
```

This is the finite exact part of the orthogonal-transform story. There is no
tolerance and no floating-point rounding.

## Replay Coordinate Zeroing

The source vector is:

```text
x = [3,4]
```

The Givens rotation zeroes its second coordinate:

```text
G*x = [5,0]
```

The transpose reconstructs the input:

```text
G^T*[5,0] = [3,4]
```

## Replay Determinant And Norm

The validator also checks:

```text
det(G) = 1
||x||^2 = 25
||G*x||^2 = 25
```

That proves the listed finite rotation behaves like an exact rotation in this
one example.

## Reject A Bad Sine Coefficient

The bad source row claims:

```text
s = 3/5
```

Exact replay computes:

```text
s = 4/5
```

The checked `QF_LRA` artifact isolates the scalar contradiction:

```text
givens_sine = 4/5
givens_sine = 3/5
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass independent
certificate checking.

## Name The Horizon

This pack does not claim:

```text
general Givens QR algorithm correctness
pivoting or rank-deficient QR behavior
least-squares theorem use
conditioning bounds
floating-point stability
```

Those require Lean theorem statements, proof-producing linear-algebra
certificates, or separate numerical-honesty artifacts.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-givens-rotation-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_givens_rotation_bad_sine_artifact_emits_checked_farkas
```

Expected output from the pack validator:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate Givens coefficients and rotation matrix
trusted small checking -> exact rational matrix products and coefficient replay
proof upgrade -> QF_LRA/Farkas certificate for the false sine claim
remaining horizon -> Givens/QR algorithms, pivoting, least squares, and stability
```

The graduation route is deterministic exact-rational finite-matrix checking
plus checked proof objects for false finite claims before broader QR or
floating-point solver claims are promoted.
