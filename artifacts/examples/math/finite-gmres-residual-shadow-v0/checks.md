# Checks

| Check | Expected | Evidence |
|---|---|---|
| `initial-residual-witness` | `sat` | replay-only |
| `krylov-direction-witness` | `sat` | replay-only |
| `one-step-gmres-minimizer-witness` | `sat` | replay-only |
| `residual-orthogonality-witness` | `sat` | replay-only |
| `residual-improvement-witness` | `sat` | replay-only |
| `bad-gmres-alpha-rejected` | `unsat` | replay-only |
| `qf-lra-bad-gmres-alpha` | `unsat` | checked |
| `general-gmres-theory-lean-horizon` | `not-run` | lean-horizon |

The first five rows are exact rational finite replay over a fixed matrix and
right-hand side. The replay-only bad row rejects the malformed one-step
coefficient after recomputation. The checked row parses the SMT-LIB artifact
and requires independently checked `UnsatFarkas` evidence.
