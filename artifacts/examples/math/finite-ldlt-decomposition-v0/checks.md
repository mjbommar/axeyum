# Checks

| Check | Expected | Evidence | Trust Story |
|---|---|---|---|
| `ldlt-shape-witness` | `sat` | replay-only | Check that `A` is symmetric, `L` is unit lower triangular, and `D` is diagonal. |
| `ldlt-product-witness` | `sat` | replay-only | Recompute `L*D*L^T` and check it equals `A`. |
| `ldlt-determinant-witness` | `sat` | replay-only | Recompute `det(A)` and the product of `D`'s diagonal entries. |
| `ldlt-positive-definite-shadow-witness` | `sat` | replay-only | Recompute the two leading principal minors for the fixed positive-definite shadow. |
| `ldlt-triangular-solve-witness` | `sat` | replay-only | Check `L*z = b`, `D*y = z`, `L^T*x = y`, and `A*x = b`. |
| `bad-ldlt-diagonal-rejected` | `unsat` | replay-only | Recompute `D[1,1] = 2` and reject the malformed `3` claim. |
| `qf-lra-bad-ldlt-diagonal` | `unsat` | checked | Parse the source SMT-LIB artifact, emit `UnsatFarkas`, and independently recheck it. |
| `general-ldlt-decomposition-theory-lean-horizon` | `not-run` | lean-horizon | LDLT existence, pivoting, indefinite variants, sparse algorithms, conditioning, and stability need theorem/numerical-honesty artifacts. |

## Source Artifact

The checked route lives in:

```text
artifacts/examples/math/finite-ldlt-decomposition-v0/smt2/bad-ldlt-diagonal-farkas-conflict.smt2
```

The route regression is:

```sh
cargo test -p axeyum-solver --test math_resource_lra_routes finite_ldlt_decomposition_bad_diagonal_artifact_emits_checked_farkas
```
