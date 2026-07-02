# Checks

| Check | Expected | Evidence |
|---|---|---|
| `initial-lanczos-vector-replay` | `sat` | replay-only |
| `first-lanczos-step-replay` | `sat` | replay-only |
| `lanczos-orthonormal-basis-replay` | `sat` | replay-only |
| `second-lanczos-step-replay` | `sat` | replay-only |
| `tridiagonal-relation-replay` | `sat` | replay-only |
| `bad-lanczos-beta1-rejected` | `unsat` | replay-only |
| `qf-lra-bad-lanczos-beta1` | `unsat` | checked |
| `general-lanczos-theory-lean-horizon` | `not-run` | Lean horizon |

The replay rows recompute symmetry, dot products, matrix-vector products, the
orthonormal basis, the tridiagonal coefficients, and the finite relation
`A*Q = Q*T` exactly.

The checked row uses:

```text
artifacts/examples/math/finite-lanczos-iteration-v0/smt2/bad-lanczos-beta1-farkas-conflict.smt2
```

That artifact asserts both `lanczos_beta1 = 1` and `lanczos_beta1 = 2`. The
solver regression must emit `Evidence::UnsatFarkas` and independently check the
certificate.
