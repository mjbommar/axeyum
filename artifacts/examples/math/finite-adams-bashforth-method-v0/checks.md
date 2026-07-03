# Checks

| Check | Expected | Proof Status | Trust Boundary |
|---|---|---|---|
| `adams-bashforth-history-witness` | `sat` | replay-only | Recompute starter value, derivative history, AB2 slopes, and updates exactly. |
| `adams-bashforth-zero-error-witness` | `sat` | replay-only | Recompute exact solution values, absolute errors, and `max_error = 0`. |
| `bad-adams-bashforth-step-rejected` | `unsat` | replay-only | Exact replay rejects the malformed first multistep value. |
| `qf-lra-bad-adams-bashforth-step` | `unsat` | checked | The source SMT-LIB row emits checked `UnsatFarkas` evidence. |
| `general-adams-bashforth-theory-lean-horizon` | `not-run` | Lean horizon | General linear multistep theory remains outside finite replay. |

The replay-only rows are educational and deterministic. They become
solver-reuse evidence only through the separate checked QF_LRA/Farkas row.
