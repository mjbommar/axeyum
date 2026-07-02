# Checks

| Check | Expected | Evidence | Purpose |
|---|---|---|---|
| `polar-shape-witness` | `sat` | replay-only | Check `U` is orthogonal and `P` is symmetric positive diagonal. |
| `polar-product-witness` | `sat` | replay-only | Recompute `U*P = A`. |
| `polar-normal-equation-witness` | `sat` | replay-only | Recompute `A^T*A = P^2`. |
| `polar-invariant-witness` | `sat` | replay-only | Recompute determinant/product and trace rows. |
| `bad-polar-diagonal-rejected` | `unsat` | replay-only | Reject the false diagonal claim by exact replay. |
| `qf-lra-bad-polar-diagonal` | `unsat` | checked | Check the scalar contradiction with Farkas evidence. |
| `general-polar-decomposition-theory-lean-horizon` | `not-run` | lean-horizon | Mark the general theorem and numerical algorithms as future work. |
