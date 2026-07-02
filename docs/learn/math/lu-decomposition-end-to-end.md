# End To End: Finite LU Decomposition

This lesson follows one exact LU factorization from data row to replayed result.
It uses
[finite-lu-decomposition-v0](../../../artifacts/examples/math/finite-lu-decomposition-v0/).

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and `curriculum_reals`
- `field_linear_algebra`, `field_numerical_analysis`, and
  `field_optimization_and_convexity`
- `bridge_lu_replay`

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `lu-unit-lower-triangular-witness` | `sat` | replay-only |
| `lu-upper-triangular-witness` | `sat` | replay-only |
| `lu-product-witness` | `sat` | replay-only |
| `lu-determinant-pivot-product-witness` | `sat` | replay-only |
| `lu-forward-back-substitution-witness` | `sat` | replay-only |
| `bad-lu-multiplier-rejected` | `unsat` | replay-only |
| `qf-lra-bad-lu-multiplier` | `unsat` | checked |
| `general-lu-decomposition-theory-lean-horizon` | `not-run` | lean-horizon |

The positive rows are exact rational replay. The checked negative row takes the
last scalar contradiction from the malformed multiplier claim and routes it
through a source SMT-LIB artifact plus rechecked `UnsatFarkas` evidence.

## Encode

The finite factorization is:

```text
A = [[2, 1],
     [4, 5]]

L = [[1, 0],
     [2, 1]]

U = [[2, 1],
     [0, 3]]
```

The checker recomputes `L*U = A`, verifies the triangular shapes, and checks the
determinant/pivot identity:

```text
det(A) = 2*5 - 1*4 = 6
U[0,0] * U[1,1] = 2 * 3 = 6
```

For `b = [5, 17]`, forward substitution gives `y = [5, 7]`, and back
substitution gives:

```text
x = [4/3, 7/3]
```

The validator checks `L*y = b`, `U*x = y`, and `A*x = b`.

## Replay

The multiplier row is intentionally tiny:

```text
l21 = A[1,0] / A[0,0] = 4 / 2 = 2
```

The malformed row says `l21 = 3`. Exact replay rejects that claim. The source
SMT-LIB artifact then forces one real-valued symbol to equal both `2` and `3`,
and the route regression requires independently rechecked Farkas evidence.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-lu-decomposition-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_lu_decomposition_bad_multiplier_artifact_emits_checked_farkas
```

Expected output for the validator:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

The untrusted side can search for factors, pivots, triangular solves, or a bad
claim. The trusted checker recomputes the small exact rational arithmetic and
checks the final linear contradiction. General LU existence, pivoting strategy,
rank-deficient variants, sparse algorithms, conditioning, and floating-point
stability stay out of this checked claim.
