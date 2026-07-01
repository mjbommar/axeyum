# Checks

| ID | Expected | Trust Status | Route |
|---|---|---|---|
| `reciprocal-tail-bounded-epsilon` | `sat` | replay-only | Replay a finite reciprocal tail below one epsilon. |
| `constant-one-limit-counterexample` | `sat` | replay-only | Replay one finite counterexample to a proposed limit. |
| `monotone-bounded-prefix` | `sat` | replay-only | Check a finite prefix is strictly increasing and bounded above. |
| `geometric-partial-sum-identity` | `sat` | replay-only | Recompute a fixed geometric sum and closed form exactly. |
| `bounded-cauchy-tail-no-counterexample` | `unsat` | checked | Exhaustively check every pair in one finite tail for one epsilon, then check the max-distance threshold contradiction through QF_LRA/Farkas. |
| `bad-reciprocal-tail-bound-rejected` | `unsat` | checked | Replay one reciprocal-tail value, then check the false strict epsilon bound through QF_LRA/Farkas. |
| `general-limit-lean-horizon` | `not-run` | lean-horizon | Keep the general convergence theorem out of the finite replay claim. |

The checked `unsat` rows are finite: they say the listed tail has no pairwise
counterexample for one epsilon and that one malformed reciprocal-tail claim is
false at a specific index. They do not assert a theorem about all future
indices.

The source SMT-LIB artifact records the final exact-rational conflict after
finite replay computes the maximum pair distance:

```text
max_pair_distance = 4/21
max_pair_distance >= 1/2
```

The `math_resource_lra_routes` regression parses
`smt2/bounded-cauchy-tail-farkas-conflict.smt2`, emits `UnsatFarkas` evidence,
and independently checks the certificate.

The bad reciprocal-tail artifact records the final strict-bound conflict after
finite replay computes `a_2 = 1/3`:

```text
tail_distance = 1/3
tail_distance < 1/4
```

The route regression parses
`smt2/bad-reciprocal-tail-bound-farkas-conflict.smt2`, emits `UnsatFarkas`
evidence, and independently checks the certificate.
