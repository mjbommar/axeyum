# Checks

| ID | Expected | Trust Status | Route |
|---|---|---|---|
| `reciprocal-tail-bounded-epsilon` | `sat` | replay-only | Replay a finite reciprocal tail below one epsilon. |
| `constant-one-limit-counterexample` | `sat` | replay-only | Replay one finite counterexample to a proposed limit. |
| `monotone-bounded-prefix` | `sat` | replay-only | Check a finite prefix is strictly increasing and bounded above. |
| `geometric-partial-sum-identity` | `sat` | replay-only | Recompute a fixed geometric sum and closed form exactly. |
| `bounded-cauchy-tail-no-counterexample` | `unsat` | checked | Exhaustively check every pair in one finite tail for one epsilon. |
| `general-limit-lean-horizon` | `not-run` | lean-horizon | Keep the general convergence theorem out of the finite replay claim. |

The checked `unsat` row is finite: it says the listed tail has no pairwise
counterexample for the listed epsilon. It does not assert a theorem about all
future indices.
