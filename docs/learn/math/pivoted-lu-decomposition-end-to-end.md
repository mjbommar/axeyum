# End To End: Finite Pivoted LU Decomposition

This lesson follows one exact row-swapped LU factorization from data row to
replayed result. It uses
[finite-pivoted-lu-decomposition-v0](../../../artifacts/examples/math/finite-pivoted-lu-decomposition-v0/).

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and `curriculum_reals`
- `field_linear_algebra`, `field_numerical_analysis`, and
  `field_optimization_and_convexity`
- `bridge_lu_replay`

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `pivoted-lu-permutation-witness` | `sat` | replay-only |
| `pivoted-lu-shape-witness` | `sat` | replay-only |
| `pivoted-lu-product-witness` | `sat` | replay-only |
| `pivoted-lu-determinant-sign-witness` | `sat` | replay-only |
| `pivoted-lu-triangular-solve-witness` | `sat` | replay-only |
| `bad-pivot-sign-rejected` | `unsat` | replay-only |
| `qf-lra-bad-pivot-sign` | `unsat` | checked |
| `general-pivoted-lu-theory-lean-horizon` | `not-run` | lean-horizon |

The positive rows are exact rational replay. The checked negative row takes the
last scalar contradiction from the malformed permutation-sign claim and routes
it through a source SMT-LIB artifact plus rechecked `UnsatFarkas` evidence.

## Encode

The finite factorization is:

```text
A = [[1, 2],
     [3, 4]]

P = [[0, 1],
     [1, 0]]

P*A = [[3, 4],
       [1, 2]]

L = [[1,   0],
     [1/3, 1]]

U = [[3, 4],
     [0, 2/3]]
```

The checker recomputes `P*A`, verifies the triangular shapes, and checks:

```text
L*U = P*A
det(P) * det(A) = (-1) * (-2) = 2
product(pivots) = 3 * (2/3) = 2
```

For `b = [3, 7]`, the pivoted right-hand side is `P*b = [7, 3]`. Forward
substitution gives `y = [7, 2/3]`, and back substitution gives:

```text
x = [1, 1]
```

The validator checks `L*y = P*b`, `U*x = y`, and `A*x = b`.

## Replay

The permutation-sign row is intentionally tiny:

```text
det(P) = -1
```

The malformed row says `det(P) = +1`. Exact replay rejects that claim. The
source SMT-LIB artifact then forces one real-valued symbol to equal both `-1`
and `+1`, and the route regression requires independently rechecked Farkas
evidence.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-pivoted-lu-decomposition-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_pivoted_lu_decomposition_bad_pivot_sign_artifact_emits_checked_farkas
```

Expected output for the validator:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

The untrusted side can search for a permutation, pivots, factors, triangular
solve, or a bad claim. The trusted checker recomputes the small exact rational
arithmetic and checks the final linear contradiction. General pivoted-LU
existence, pivot-selection strategy, rank-deficient variants, sparse pivoting,
growth-factor bounds, conditioning, and floating-point stability stay out of
this checked claim.
