# Checks

| ID | Expected | Trust Status | Route |
|---|---|---|---|
| `reciprocal-tail-bounded-epsilon` | `sat` | replay-only | Replay a finite reciprocal tail below one epsilon. |
| `constant-one-limit-counterexample` | `sat` | replay-only | Replay one finite counterexample to a proposed limit. |
| `monotone-bounded-prefix` | `sat` | replay-only | Check a finite prefix is strictly increasing and bounded above. |
| `geometric-partial-sum-identity` | `sat` | replay-only | Recompute a fixed geometric sum and closed form exactly. |
| `bounded-cauchy-tail-no-counterexample` | `unsat` | checked | Exhaustively check every pair in one finite tail for one epsilon, then check the max-distance threshold contradiction through QF_LRA/Farkas. |
| `general-limit-lean-horizon` | `not-run` | lean-horizon | Keep the general convergence theorem out of the finite replay claim. |

The checked `unsat` row is finite: it says the listed tail has no pairwise
counterexample for the listed epsilon. It does not assert a theorem about all
future indices.

The source SMT-LIB artifact records the final exact-rational conflict after
finite replay computes the maximum pair distance:

```text
max_pair_distance = 4/21
max_pair_distance >= 1/2
```

The `math_resource_lra_routes` regression parses
`smt2/bounded-cauchy-tail-farkas-conflict.smt2`, emits `UnsatFarkas` evidence,
and independently checks the certificate.
