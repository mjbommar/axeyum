# Checks

| Check | Expected | Evidence | Purpose |
|---|---|---|---|
| `orthogonal-matrix-witness` | `sat` | replay-only | Recompute `Q^T*Q`, `Q*Q^T`, and column norms/dots. |
| `orthogonal-diagonalization-witness` | `sat` | replay-only | Recompute `Q*D*Q^T = A` and check shape side conditions. |
| `spectral-eigenpair-witness` | `sat` | replay-only | Check both column eigenpairs exactly. |
| `spectral-invariant-witness` | `sat` | replay-only | Check trace and determinant against the listed eigenvalues. |
| `bad-spectral-eigenvalue-rejected` | `unsat` | replay-only | Reject the malformed eigenvalue claim by exact replay. |
| `qf-lra-bad-spectral-eigenvalue` | `unsat` | checked | Parse the source SMT-LIB contradiction and require checked Farkas evidence. |
| `general-orthogonal-diagonalization-theory-lean-horizon` | `not-run` | lean-horizon | Keep the general theorem and numerical-eigensolver claims out of the finite row. |

Source artifact:

```text
artifacts/examples/math/finite-orthogonal-diagonalization-v0/smt2/bad-spectral-eigenvalue-farkas-conflict.smt2
```
