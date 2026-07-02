# Checks

| Check | Expected | Evidence | Purpose |
|---|---|---|---|
| `shifted-qr-shape-witness` | `sat` | replay-only | Check `Q` is orthogonal and `R` is upper triangular. |
| `shifted-qr-factorization-witness` | `sat` | replay-only | Recompute `A0 - mu*I = Q*R`. |
| `shifted-qr-update-witness` | `sat` | replay-only | Recompute `A1 = R*Q + mu*I`. |
| `shifted-qr-similarity-witness` | `sat` | replay-only | Recompute `Q^T*A0*Q = A1`. |
| `shifted-qr-invariant-witness` | `sat` | replay-only | Recompute trace and determinant invariants across the shifted step. |
| `bad-shifted-qr-entry-rejected` | `unsat` | replay-only | Reject the false shifted-step matrix entry by exact replay. |
| `qf-lra-bad-shifted-qr-entry` | `unsat` | checked | Check the scalar contradiction with Farkas evidence. |
| `general-shifted-qr-theory-lean-horizon` | `not-run` | lean-horizon | Mark shift strategy, convergence, deflation, and stability theory as future work. |
