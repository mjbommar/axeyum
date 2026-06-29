# Checks

| Check | Result | Evidence |
|---|---|---|
| `standard-inner-product-replay` | `sat` | Recompute fixed dot products and sample bilinearity over `Q^2`. |
| `gram-matrix-positive-definite` | `sat` | Check symmetry and exact leading principal minors. |
| `cauchy-schwarz-fixed-vectors` | `sat` | Recompute both sides of a fixed Cauchy-Schwarz inequality. |
| `orthogonal-projection-replay` | `sat` | Recompute projection coefficient, residual, orthogonality, and norm split. |
| `gram-schmidt-replay` | `sat` | Recompute the second projection/residual and check orthogonality. |
| `bad-inner-product-rejected` | `unsat` | Reject a Gram matrix with a negative norm square. |
| `general-inner-product-theory-lean-horizon` | `not-run` | Names the Lean route for general inner-product and Hilbert-space theory. |

The checked rows are exact finite-dimensional arithmetic rows. They are not
claims about arbitrary inner-product spaces.
