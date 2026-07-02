# Checks

| Check | Expected | Evidence | Purpose |
|---|---|---|---|
| `schur-shape-witness` | `sat` | replay-only | Recompute `Q^T*Q`, `Q*Q^T`, and upper-triangular shape for `T`. |
| `schur-reconstruction-witness` | `sat` | replay-only | Recompute `Q*T*Q^T = A`. |
| `schur-vector-relation-witness` | `sat` | replay-only | Recompute `A*Q = Q*T` and the listed column relations. |
| `schur-invariant-witness` | `sat` | replay-only | Check trace and determinant against the diagonal of `T`. |
| `bad-schur-superdiagonal-rejected` | `unsat` | replay-only | Reject the malformed superdiagonal-entry claim by exact replay. |
| `qf-lra-bad-schur-superdiagonal` | `unsat` | checked | Parse the source SMT-LIB contradiction and require checked Farkas evidence. |
| `general-real-schur-theory-lean-horizon` | `not-run` | lean-horizon | Keep the general Schur theorem and numerical eigensolver claims out of the finite row. |

Source artifact:

```text
artifacts/examples/math/finite-real-schur-decomposition-v0/smt2/bad-schur-superdiagonal-farkas-conflict.smt2
```
