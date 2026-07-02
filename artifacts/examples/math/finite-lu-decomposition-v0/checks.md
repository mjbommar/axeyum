# Checks

| Check | Expected | Evidence | Trust Story |
|---|---|---|---|
| `lu-unit-lower-triangular-witness` | `sat` | replay-only | Check that `L` is unit lower triangular. |
| `lu-upper-triangular-witness` | `sat` | replay-only | Check that `U` is upper triangular. |
| `lu-product-witness` | `sat` | replay-only | Recompute `L U` and check it equals `A`. |
| `lu-determinant-pivot-product-witness` | `sat` | replay-only | Recompute `det(A)` and the pivot product `2 * 3`. |
| `lu-forward-back-substitution-witness` | `sat` | replay-only | Recompute `L*y = b`, `U*x = y`, and `A*x = b`. |
| `bad-lu-multiplier-rejected` | `unsat` | replay-only | Recompute the elimination multiplier as `4 / 2 = 2` and reject the malformed `3` claim. |
| `qf-lra-bad-lu-multiplier` | `unsat` | checked | Parse the source SMT-LIB artifact, emit `UnsatFarkas`, and independently recheck it. |
| `general-lu-decomposition-theory-lean-horizon` | `not-run` | lean-horizon | LU existence, pivoting, rank-deficient cases, sparse algorithms, conditioning, and stability need theorem/numerical-honesty artifacts. |

## Source Artifact

The checked route lives in:

```text
artifacts/examples/math/finite-lu-decomposition-v0/smt2/bad-lu-multiplier-farkas-conflict.smt2
```

The route regression is:

```sh
cargo test -p axeyum-solver --test math_resource_lra_routes finite_lu_decomposition_bad_multiplier_artifact_emits_checked_farkas
```
