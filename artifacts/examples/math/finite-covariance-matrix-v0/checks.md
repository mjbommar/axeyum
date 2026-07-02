# Checks

| Check | Expected | Evidence | Trust Story |
|---|---|---|---|
| `sample-mean-vector-witness` | `sat` | replay-only | Recompute the fixed sample mean vector exactly. |
| `centered-sample-witness` | `sat` | replay-only | Subtract the mean from every row and check the centered rows sum to zero. |
| `covariance-matrix-witness` | `sat` | replay-only | Recompute the centered Gram matrix and covariance matrix over exact rationals. |
| `covariance-positive-semidefinite-shadow-witness` | `sat` | replay-only | Recompute the two leading principal minors and check they are positive. |
| `bad-covariance-entry-rejected` | `unsat` | replay-only | Recompute the off-diagonal covariance entry as `4/9` and reject the malformed `1/2` claim. |
| `qf-lra-bad-covariance-entry` | `unsat` | checked | Parse the source SMT-LIB artifact, emit `UnsatFarkas`, and independently recheck it. |
| `general-covariance-statistics-lean-horizon` | `not-run` | lean-horizon | Statistical inference, PCA, asymptotic covariance theory, and floating-point covariance algorithms need theorem/numerical-honesty artifacts. |

## Source Artifact

The checked route lives in:

```text
artifacts/examples/math/finite-covariance-matrix-v0/smt2/bad-covariance-entry-farkas-conflict.smt2
```

The route regression is:

```sh
cargo test -p axeyum-solver --test math_resource_lra_routes finite_covariance_matrix_bad_entry_artifact_emits_checked_farkas
```
