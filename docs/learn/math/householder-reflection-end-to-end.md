# End To End: Finite Householder Reflection

This lesson follows one exact finite Householder reflection resource from a raw
reflector vector to an orthogonal reflection matrix, a zeroed vector, an
involution replay, and a checked bad-entry rejection. It uses the
[finite-householder-reflection-v0](../../../artifacts/examples/math/finite-householder-reflection-v0/)
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
| `householder-formula-witness` | `sat` | replay-only |
| `householder-orthogonality-witness` | `sat` | replay-only |
| `householder-zeroing-witness` | `sat` | replay-only |
| `householder-involution-witness` | `sat` | replay-only |
| `householder-determinant-witness` | `sat` | replay-only |
| `bad-householder-entry-rejected` | `unsat` | replay-only |
| `qf-lra-bad-householder-entry` | `unsat` | checked |
| `general-householder-qr-theory-lean-horizon` | `not-run` | Lean horizon |

The pack uses the exact rational reflector vector:

```text
v = [2,1]
v^T*v = 5
```

and the reflection:

```text
H = I - 2*v*v^T/(v^T*v)
  = [[-3/5, -4/5],
     [-4/5,  3/5]]
```

## Replay The Formula

The validator recomputes every entry of:

```text
I - 2*v*v^T/(v^T*v)
```

and compares it with the listed matrix. This keeps the check tied to the
Householder construction, not just to an arbitrary two-by-two matrix.

## Replay Orthogonality

The validator checks:

```text
H^T = H
H^T*H = I
```

This is the finite exact part of the reflection story. There is no tolerance
and no floating-point rounding.

## Replay Coordinate Zeroing

The source vector is:

```text
x = [3,4]
```

The Householder reflection zeroes its second coordinate:

```text
H*x = [-5,0]
```

Applying the reflection again reconstructs the input:

```text
H*[-5,0] = [3,4]
```

## Replay Determinant And Norm

The validator also checks:

```text
det(H) = -1
||x||^2 = 25
||H*x||^2 = 25
```

That proves the listed finite reflection behaves like an exact Householder
reflection in this one example.

## Reject A Bad Matrix Entry

The bad source row claims:

```text
H[0,0] = -4/5
```

Exact replay computes:

```text
H[0,0] = -3/5
```

The checked `QF_LRA` artifact isolates the scalar contradiction:

```text
householder_entry_00 = -3/5
householder_entry_00 = -4/5
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass independent
certificate checking.

## Name The Horizon

This pack does not claim:

```text
general Householder QR algorithm correctness
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
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-householder-reflection-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_householder_reflection_bad_entry_artifact_emits_checked_farkas
```

Expected output from the pack validator:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate reflector vector and reflection matrix
trusted small checking -> exact rational matrix products and formula replay
proof upgrade -> QF_LRA/Farkas certificate for the false entry claim
remaining horizon -> Householder/QR algorithms, pivoting, least squares, and stability
```

The graduation route is deterministic exact-rational finite-matrix checking
plus checked proof objects for false finite claims before broader QR or
floating-point solver claims are promoted.
