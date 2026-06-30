# Checks

| Check | Result | Evidence |
|---|---|---|
| `factorization-product-replay` | `sat` | Multiply the listed rational factors and compare normalized coefficients. |
| `polynomial-division-replay` | `sat` | Recompute quotient and zero remainder for division by `x - 1`. |
| `euclidean-gcd-replay` | `sat` | Recompute a monic Euclidean GCD over `Q[x]`. |
| `square-free-decomposition-replay` | `sat` | Recompute `p'`, `gcd(p,p')`, and the square-free quotient. |
| `irreducible-quadratic-rational-rejected` | `unsat` | Reject rational linear factorization for `x^2 + 1` by exact discriminant replay. |
| `irreducible-quadratic-discriminant-conflict` | `unsat` | Check the replayed discriminant `-4` against the nonnegative-discriminant requirement with QF_LRA/Farkas evidence. |
| `general-factorization-theory-lean-horizon` | `not-run` | Names the Lean/library route for arbitrary-field factorization theory. |

The checked rows are fixed exact polynomial arithmetic rows. They do not claim
a complete factorization algorithm for arbitrary fields or degrees.
