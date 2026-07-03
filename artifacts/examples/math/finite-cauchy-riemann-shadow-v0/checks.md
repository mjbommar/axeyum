# Checks

| Check | Expected | Evidence |
|---|---|---|
| `complex-square-real-pair-witness` | `sat` | replay-only |
| `partial-derivative-witness` | `sat` | replay-only |
| `cauchy-riemann-equality-witness` | `sat` | replay-only |
| `complex-derivative-witness` | `sat` | replay-only |
| `bad-derivative-real-part-rejected` | `unsat` | replay-only |
| `qf-lra-bad-derivative-real-part` | `unsat` | checked |
| `general-cauchy-riemann-lean-horizon` | `not-run` | lean-horizon |

The first four rows are exact finite replay over rational real-pair and
bivariate polynomial data. The replay-only bad row rejects the malformed
derivative component after recomputation. The checked row parses the SMT-LIB
artifact and requires independently checked `UnsatFarkas` evidence.
