# Checks

| Check | Expected | Evidence | Purpose |
|---|---|---|---|
| `qr-step-shape-witness` | `sat` | replay-only | Check `Q` is orthogonal and `R` is upper triangular. |
| `qr-step-factorization-witness` | `sat` | replay-only | Recompute `Q*R = A0`. |
| `qr-step-update-witness` | `sat` | replay-only | Recompute `R*Q = A1`. |
| `qr-step-similarity-witness` | `sat` | replay-only | Recompute `Q^T*A0*Q = A1`. |
| `qr-step-invariant-witness` | `sat` | replay-only | Recompute trace and determinant invariants across the step. |
| `bad-qr-step-entry-rejected` | `unsat` | replay-only | Reject the false next-step matrix entry by exact replay. |
| `qf-lra-bad-qr-step-entry` | `unsat` | checked | Check the scalar contradiction with Farkas evidence. |
| `general-qr-iteration-theory-lean-horizon` | `not-run` | lean-horizon | Mark convergence, shift, Schur, and stability theory as future work. |
