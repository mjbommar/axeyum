# Checks

| Check | Expected | Evidence | Trust Story |
|---|---|---|---|
| `qr-orthogonality-witness` | `sat` | replay-only | Recompute `Q^T Q` and check it equals the identity matrix. |
| `qr-upper-triangular-witness` | `sat` | replay-only | Check the fixed lower-triangular entries of `R` are zero. |
| `qr-product-witness` | `sat` | replay-only | Recompute `Q R` and check it equals the listed matrix `A`. |
| `bad-qr-product-entry-rejected` | `unsat` | replay-only | Recompute the bottom-right product entry as `2/5` and reject the malformed `1/2` claim. |
| `qf-lra-bad-qr-product-entry` | `unsat` | checked | Parse the source SMT-LIB artifact, emit `UnsatFarkas`, and independently recheck it. |
| `general-qr-decomposition-theory-lean-horizon` | `not-run` | lean-horizon | QR existence, uniqueness conventions, algorithm correctness, conditioning, and stability need theorem/numerical-honesty artifacts. |

## Source Artifact

The checked route lives in:

```text
artifacts/examples/math/finite-qr-decomposition-v0/smt2/bad-qr-product-entry-farkas-conflict.smt2
```

The route regression is:

```sh
cargo test -p axeyum-solver --test math_resource_lra_routes finite_qr_decomposition_bad_product_entry_artifact_emits_checked_farkas
```
