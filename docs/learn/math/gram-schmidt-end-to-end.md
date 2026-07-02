# End To End: Finite Gram-Schmidt

This lesson follows one exact finite Gram-Schmidt resource from two rational
input columns to normalized vectors, a projection coefficient, an
upper-triangular factor, a QR product replay, and a checked bad-coefficient
rejection. It uses the
[finite-gram-schmidt-v0](../../../artifacts/examples/math/finite-gram-schmidt-v0/)
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
| `gram-schmidt-first-vector-witness` | `sat` | replay-only |
| `gram-schmidt-projection-witness` | `sat` | replay-only |
| `gram-schmidt-orthonormality-witness` | `sat` | replay-only |
| `gram-schmidt-upper-triangular-witness` | `sat` | replay-only |
| `gram-schmidt-qr-product-witness` | `sat` | replay-only |
| `bad-gram-schmidt-r12-rejected` | `unsat` | replay-only |
| `qf-lra-bad-gram-schmidt-r12` | `unsat` | checked |
| `general-gram-schmidt-qr-theory-lean-horizon` | `not-run` | Lean horizon |

The pack uses two exact rational input columns:

```text
a1 = [3,4]
a2 = [1,0]
```

## Replay The First Normalization

The validator checks:

```text
r11 = 5
q1 = [3/5,4/5]
r11*q1 = a1
q1 dot q1 = 1
```

This avoids a floating-point square-root call. The listed rational data must
replay exactly.

## Replay The Projection Step

The projection coefficient is:

```text
r12 = q1 dot a2 = 3/5
```

The residual is:

```text
u2 = a2 - r12*q1 = [16/25,-12/25]
```

The second normalization is:

```text
r22 = 4/5
q2 = [4/5,-3/5]
```

The validator recomputes each of those equalities and checks that `u2` is
orthogonal to `q1`.

## Replay QR

The resulting matrices are:

```text
Q = [[3/5,  4/5],
     [4/5, -3/5]]

R = [[5, 3/5],
     [0, 4/5]]
```

The validator checks:

```text
Q^T*Q = I
Q*R = [[3,1],
       [4,0]]
```

## Reject A Bad Projection Coefficient

The bad source row claims:

```text
r12 = 4/5
```

Exact replay computes:

```text
r12 = 3/5
```

The checked `QF_LRA` artifact isolates the scalar contradiction:

```text
gram_schmidt_r12 = 3/5
gram_schmidt_r12 = 4/5
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass independent
certificate checking.

## Name The Horizon

This pack does not claim:

```text
general Gram-Schmidt correctness
rank-deficient QR behavior
modified Gram-Schmidt stability
least-squares theorem use
floating-point loss of orthogonality
```

Those require Lean theorem statements, proof-producing linear-algebra
certificates, or separate numerical-honesty artifacts.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-gram-schmidt-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_gram_schmidt_bad_r12_artifact_emits_checked_farkas
```

Expected output from the pack validator:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate projection coefficient, Q, and R
trusted small checking -> exact rational dot products and matrix products
proof upgrade -> QF_LRA/Farkas certificate for the false r12 claim
remaining horizon -> Gram-Schmidt/QR algorithms, rank deficiency, least squares, and stability
```

The graduation route is deterministic exact-rational finite-matrix checking
plus checked proof objects for false finite claims before broader QR or
floating-point solver claims are promoted.
