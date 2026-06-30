# Checks

| Check | Result | Proof status | What is checked |
|---|---:|---|---|
| `integer-chain-complex-replay` | `sat` | `replay-only` | Boundary matrix shapes and `d0*d1 = 0`. |
| `smith-normal-form-replay` | `sat` | `replay-only` | Rank, one-entry Smith diagonal, free-rank bookkeeping, and the `Z/2` torsion factor. |
| `torsion-generator-replay` | `sat` | `replay-only` | `d1(1*e) = 2v` and non-divisibility of `1` by `2`. |
| `bad-torsion-boundary-rejected` | `unsat` | `checked` | Exact replay rejects the false claim that `v` is in `im(d1)`. |
| `qf-lia-bad-torsion-generator` | `unsat` | `checked` | The source SMT-LIB equation `2*k = 1` emits checked `UnsatDiophantine` evidence. |
| `general-universal-coefficient-lean-horizon` | `not-run` | `lean-horizon` | Records theorem families that require future Lean proof resources. |

This is an integer torsion resource, not a general algebraic-topology theorem.
The validator is allowed to trust only the finite data listed in
`expected.json` and the independently checked QF_LIA certificate route.
