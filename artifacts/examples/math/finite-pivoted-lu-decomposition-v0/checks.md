# Checks

| Check | Expected | Evidence | Trust Story |
|---|---|---|---|
| `pivoted-lu-permutation-witness` | `sat` | replay-only | Check that `P` is a row-swap permutation and recompute `P*A` and `P*b`. |
| `pivoted-lu-shape-witness` | `sat` | replay-only | Check that `L` is unit lower triangular and `U` is upper triangular. |
| `pivoted-lu-product-witness` | `sat` | replay-only | Recompute `L*U` and check it equals `P*A`. |
| `pivoted-lu-determinant-sign-witness` | `sat` | replay-only | Recompute `det(P)`, `det(A)`, and the pivot product. |
| `pivoted-lu-triangular-solve-witness` | `sat` | replay-only | Check `L*y = P*b`, `U*x = y`, and `A*x = b`. |
| `bad-pivot-sign-rejected` | `unsat` | replay-only | Recompute the row-swap determinant as `-1` and reject the malformed `+1` claim. |
| `qf-lra-bad-pivot-sign` | `unsat` | checked | Parse the source SMT-LIB artifact, emit `UnsatFarkas`, and independently recheck it. |
| `general-pivoted-lu-theory-lean-horizon` | `not-run` | lean-horizon | Pivoting strategy correctness, rank-deficient cases, sparse pivots, growth factors, conditioning, and stability need theorem/numerical-honesty artifacts. |

## Source Artifact

The checked route lives in:

```text
artifacts/examples/math/finite-pivoted-lu-decomposition-v0/smt2/bad-pivot-sign-farkas-conflict.smt2
```

The route regression is:

```sh
cargo test -p axeyum-solver --test math_resource_lra_routes finite_pivoted_lu_decomposition_bad_pivot_sign_artifact_emits_checked_farkas
```
