# End To End: Finite LDLT Decomposition

This lesson follows one exact LDLT factorization from data row to replayed
result. It uses
[finite-ldlt-decomposition-v0](../../../artifacts/examples/math/finite-ldlt-decomposition-v0/).

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and `curriculum_reals`
- `field_linear_algebra`, `field_numerical_analysis`, and
  `field_optimization_and_convexity`
- `bridge_lu_replay`

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `ldlt-shape-witness` | `sat` | replay-only |
| `ldlt-product-witness` | `sat` | replay-only |
| `ldlt-determinant-witness` | `sat` | replay-only |
| `ldlt-positive-definite-shadow-witness` | `sat` | replay-only |
| `ldlt-triangular-solve-witness` | `sat` | replay-only |
| `bad-ldlt-diagonal-rejected` | `unsat` | replay-only |
| `qf-lra-bad-ldlt-diagonal` | `unsat` | checked |
| `general-ldlt-decomposition-theory-lean-horizon` | `not-run` | lean-horizon |

The positive rows are exact rational replay. The checked negative row takes the
last scalar contradiction from the malformed diagonal-entry claim and routes it
through a source SMT-LIB artifact plus rechecked `UnsatFarkas` evidence.

## Encode

The finite factorization is:

```text
A = [[4, 2],
     [2, 3]]

L = [[1,   0],
     [1/2, 1]]

D = [[4, 0],
     [0, 2]]

L^T = [[1, 1/2],
       [0, 1]]
```

The checker verifies that `A` is symmetric, `L` is unit lower triangular, and
`D` is diagonal. It then recomputes:

```text
L*D*L^T = A
det(A) = 8
product(diag(D)) = 8
leading principal minors = [4, 8]
```

For `b = [6, 5]`, the solve is:

```text
L*z = b      gives z = [6, 2]
D*y = z      gives y = [3/2, 1]
L^T*x = y    gives x = [1, 1]
```

The validator checks `A*x = b`.

## Replay

The malformed row is intentionally tiny:

```text
D[1,1] = 3
```

Exact replay computes `D[1,1] = 2`. The source SMT-LIB artifact forces one
real-valued symbol to equal both `2` and `3`, and the route regression requires
independently rechecked Farkas evidence.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-ldlt-decomposition-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_ldlt_decomposition_bad_diagonal_artifact_emits_checked_farkas
```

Expected output for the validator:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

The untrusted side can search for symmetric factors, pivots, triangular solves,
or a bad claim. The trusted checker recomputes the small exact rational
arithmetic and checks the final linear contradiction. General LDLT existence,
pivoted indefinite LDLT, rank-deficient variants, sparse factorization,
conditioning, and floating-point stability stay out of this checked claim.
