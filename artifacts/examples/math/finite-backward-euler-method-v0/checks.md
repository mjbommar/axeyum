# Checks

| Check | Expected | Proof Status | Trust Boundary |
|---|---|---|---|
| `backward-euler-implicit-solve-witness` | `sat` | replay-only | Recompute endpoint times, endpoint derivatives, implicit residuals, and updates exactly. |
| `backward-euler-geometric-decay-witness` | `sat` | replay-only | Recompute the finite ratio `2/3`, bounds, positivity, and monotone decrease on the listed trace. |
| `bad-backward-euler-step-rejected` | `unsat` | replay-only | Exact replay rejects the malformed first-step value. |
| `qf-lra-bad-backward-euler-step` | `unsat` | checked | The source SMT-LIB row emits checked `UnsatFarkas` evidence. |
| `general-backward-euler-theory-lean-horizon` | `not-run` | Lean horizon | General implicit-method theory remains outside finite replay. |

The replay-only rows are educational and deterministic. They become
solver-reuse evidence only through the separate checked QF_LRA/Farkas row.
