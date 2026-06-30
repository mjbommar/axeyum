# Checks

| Check | Expected | Evidence |
|---|---|---|
| `finite-quadratic-grid-minimum-replay` | `sat` | replay-only |
| `kkt-stationarity-replay` | `sat` | replay-only |
| `complementary-slackness-replay` | `sat` | replay-only |
| `bad-kkt-stationarity-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-kkt-sufficiency-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only the listed finite rational quadratic instance and
KKT witness. The bad row keeps the replayed stationarity error fixed and checks
a tiny linear contradiction.
