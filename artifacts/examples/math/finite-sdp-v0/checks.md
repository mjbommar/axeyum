# Checks

| Check | Expected | Evidence |
|---|---|---|
| `finite-sdp-primal-psd-replay` | `sat` | replay-only |
| `finite-sdp-objective-replay` | `sat` | replay-only |
| `finite-sdp-dual-slack-replay` | `sat` | replay-only |
| `bad-sdp-objective-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-sdp-duality-gap-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-sdp-duality-lean-horizon` | `not-run` | Lean horizon |

The replay rows check only the listed rational two-by-two SDP witness. The bad
rows keep the replayed objective or duality-gap error fixed and check tiny
linear contradictions.
