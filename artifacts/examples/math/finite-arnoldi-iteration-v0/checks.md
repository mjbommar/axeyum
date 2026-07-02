# Checks

| Check | Expected | Evidence |
|---|---|---|
| `initial-krylov-vector-replay` | `sat` | replay-only |
| `first-arnoldi-projection-replay` | `sat` | replay-only |
| `arnoldi-orthonormal-basis-replay` | `sat` | replay-only |
| `second-column-hessenberg-replay` | `sat` | replay-only |
| `hessenberg-relation-replay` | `sat` | replay-only |
| `bad-arnoldi-h21-rejected` | `unsat` | replay-only |
| `qf-lra-bad-arnoldi-h21` | `unsat` | checked |
| `general-arnoldi-gmres-theory-lean-horizon` | `not-run` | Lean horizon |

The replay rows recompute dot products, matrix-vector products, the
orthonormal basis, the Hessenberg coefficients, and the finite relation
`A*Q = Q*H` exactly.

The checked row uses:

```text
artifacts/examples/math/finite-arnoldi-iteration-v0/smt2/bad-arnoldi-h21-farkas-conflict.smt2
```

That artifact asserts both `arnoldi_h21 = 3` and `arnoldi_h21 = 2`. The
solver regression must emit `Evidence::UnsatFarkas` and independently check the
certificate.
