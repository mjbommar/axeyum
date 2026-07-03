# Checks

| Check | Expected | Proof Status | Trust Boundary |
|---|---|---|---|
| `crank-nicolson-implicit-trapezoid-witness` | `sat` | replay-only | Recompute start derivatives, endpoint derivatives, averaged slopes, and implicit residuals exactly. |
| `crank-nicolson-geometric-decay-witness` | `sat` | replay-only | Recompute the finite positive decreasing trace and ratio `3/5`. |
| `bad-crank-nicolson-step-rejected` | `unsat` | replay-only | Exact replay rejects the malformed first-step value. |
| `qf-lra-bad-crank-nicolson-step` | `unsat` | checked | The source SMT-LIB row emits checked `UnsatFarkas` evidence. |
| `general-crank-nicolson-theory-lean-horizon` | `not-run` | Lean horizon | General Crank-Nicolson theory remains outside finite replay. |

The replay-only rows are educational and deterministic. They become
solver-reuse evidence only through the separate checked QF_LRA/Farkas row.
