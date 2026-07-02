# Checks

| Check | Expected | Evidence |
|---|---|---|
| `gram-schmidt-first-vector-witness` | `sat` | replay-only |
| `gram-schmidt-projection-witness` | `sat` | replay-only |
| `gram-schmidt-orthonormality-witness` | `sat` | replay-only |
| `gram-schmidt-upper-triangular-witness` | `sat` | replay-only |
| `gram-schmidt-qr-product-witness` | `sat` | replay-only |
| `bad-gram-schmidt-r12-rejected` | `unsat` | replay-only |
| `qf-lra-bad-gram-schmidt-r12` | `unsat` | checked |
| `general-gram-schmidt-qr-theory-lean-horizon` | `not-run` | Lean horizon |

The replay rows recompute the first normalization, projection coefficient,
residual vector, second normalization, orthonormality, triangularity, and QR
product exactly.

The checked row uses:

```text
artifacts/examples/math/finite-gram-schmidt-v0/smt2/bad-gram-schmidt-r12-farkas-conflict.smt2
```

That artifact asserts both `gram_schmidt_r12 = 3/5` and
`gram_schmidt_r12 = 4/5`. The solver regression must emit
`Evidence::UnsatFarkas` and independently check the certificate.
