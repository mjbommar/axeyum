# Checks

| Check | Expected | Evidence | Trust Story |
|---|---|---|---|
| `cholesky-lower-triangular-witness` | `sat` | replay-only | Check the fixed above-diagonal entries of `L` are zero. |
| `cholesky-positive-diagonal-witness` | `sat` | replay-only | Check the fixed diagonal entries of `L` are positive. |
| `cholesky-product-witness` | `sat` | replay-only | Recompute `L L^T` and check it equals the listed matrix `A`. |
| `cholesky-positive-definite-shadow-witness` | `sat` | replay-only | Recompute the two leading principal minors and check they are positive. |
| `bad-cholesky-product-entry-rejected` | `unsat` | replay-only | Recompute the bottom-right product entry as `10` and reject the malformed `9` claim. |
| `qf-lra-bad-cholesky-product-entry` | `unsat` | checked | Parse the source SMT-LIB artifact, emit `UnsatFarkas`, and independently recheck it. |
| `general-cholesky-decomposition-theory-lean-horizon` | `not-run` | lean-horizon | Cholesky existence, uniqueness conventions, algorithm correctness, conditioning, and stability need theorem/numerical-honesty artifacts. |

## Source Artifact

The checked route lives in:

```text
artifacts/examples/math/finite-cholesky-decomposition-v0/smt2/bad-cholesky-product-entry-farkas-conflict.smt2
```

The route regression is:

```sh
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cholesky_decomposition_bad_product_entry_artifact_emits_checked_farkas
```
