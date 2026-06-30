# Checks

| Check | Result | Proof status | What is checked |
|---|---:|---|---|
| `integer-cochain-complex-replay` | `sat` | `replay-only` | `delta0 = d1^T`, zero cochain composition, `H^0 = 0`, and `H^1 = Z/2`. |
| `degree-one-uct-shadow` | `sat` | `replay-only` | `Hom(H1,Z)=0`, `Ext(H0,Z)=Z/2`, and the fixed short exact-sequence shape. |
| `bad-uct-zero-rejected` | `unsat` | `checked` | Replayed group invariants reject the false claim `H^1 = 0`. |
| `qf-uf-bad-uct-h1-zero` | `unsat` | `checked` | The source SMT-LIB equality conflict emits checked `UnsatAletheProof` evidence. |
| `general-uct-theorem-lean-horizon` | `not-run` | `lean-horizon` | Records theorem families that require future Lean proof resources. |

The trusted boundary is finite invariant replay plus checked equality evidence
for the final malformed group-identification row. General universal
coefficient theorem statements remain proof-assistant targets.
