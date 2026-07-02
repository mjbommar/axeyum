# Checks

| Check | Expected | Evidence |
|---|---|---|
| `givens-orthogonality-witness` | `sat` | replay-only |
| `givens-zeroing-witness` | `sat` | replay-only |
| `givens-inverse-reconstruction-witness` | `sat` | replay-only |
| `givens-determinant-witness` | `sat` | replay-only |
| `bad-givens-sine-rejected` | `unsat` | replay-only |
| `qf-lra-bad-givens-sine` | `unsat` | checked |
| `general-givens-qr-theory-lean-horizon` | `not-run` | Lean horizon |

The replay rows recompute the transpose, orthogonality, the zeroing product,
inverse reconstruction, determinant, and squared norms exactly.

The checked row uses:

```text
artifacts/examples/math/finite-givens-rotation-v0/smt2/bad-givens-sine-farkas-conflict.smt2
```

That artifact asserts both `givens_sine = 4/5` and `givens_sine = 3/5`. The
solver regression must emit `Evidence::UnsatFarkas` and independently check the
certificate.
