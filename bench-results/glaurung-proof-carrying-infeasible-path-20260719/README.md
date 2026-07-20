# Glaurung proof-carrying infeasible path — 2026-07-19

Status: accepted as one bounded downstream proof-consumer demonstration

Glaurung commit `f01a057` replaces its discarded DRAT-line-count prototype
with an `InfeasiblePathVerdict`. The infeasible variant owns the exact Axeyum
certificate, and `recheck_for_path` retranslates the supplied Glaurung
`ExprPool` assertions, requires byte-identical CNF, and independently rechecks
DRAT/LRAT. A proof for `x == 5 AND x == 6` rechecks against that exact path and
returns false against the weakened satisfiable path `x == 5`.

The fixed release example ran once from committed source and emitted:

| File | Bytes | SHA-256 |
|---|---:|---|
| [`manifest.json`](manifest.json) | 749 | `4bdecf5b...825e` |
| [`problem.cnf`](problem.cnf) | 202 | `9ce48e7c...7cb6` |
| [`proof.drat`](proof.drat) | 2 | `9a271f2a...86aa` |
| [`proof.lrat`](proof.lrat) | 13 | `73c591f0...8bd5` |

The example executable SHA-256 was `a7998ca9...c628`. The source identities are
Axeyum `a249fbe4`, Glaurung base `403a5c5`, and Glaurung implementation
`f01a057`.

Pinned upstream `drat-trim` (`2e3b2dc0`, binary SHA-256 `c0b9bd6a...9db`)
accepts `problem.cnf + proof.drat` with exit 0 and exact `s VERIFIED`. The same
proof against [`satisfiable-control.cnf`](satisfiable-control.cnf) exits 1,
reports `no conflict`, and prints `s NOT VERIFIED`. [`result.json`](result.json)
retains exit codes, hashes, and base64-encoded exact stdout streams.

## Honest scope

This is a real Glaurung-native path verdict with an attached, source-rebound,
externally consumed certificate. It is intentionally not presented as more:

- the CNF is input-refutable by complementary unit clauses;
- the DRAT is the two-byte empty-clause line, not a nontrivial learned trace;
- one path conjunction is not a proof that every CFG path to a target was
  exhaustively enumerated; and
- external DRAT checks the clausal layer, while term-to-AIG-to-CNF remains the
  documented trusted reduction.

The result closes the reviewer checklist's minimal "demonstrate a downstream
proof-carrying use" cell. Proof prevalence, whole-CFG certificate composition,
and cost/benefit at census scale remain separate questions.
