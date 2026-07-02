# Checks

| Check | Result | Evidence |
|---|---|---|
| `c2-swap-action-laws` | `sat` | Check identity action and action compatibility over all table entries. |
| `orbit-stabilizer-replay` | `sat` | Recompute the orbit and stabilizer of `01`, then check `|orbit|*|stabilizer|=|G|`. |
| `burnside-orbit-count-replay` | `sat` | Recompute fixed-point counts for `e` and `s`, then check the Burnside average. |
| `bad-action-rejected` | `unsat` | Exact finite replay rejects a malformed action table that violates the identity action. |
| `qf-uf-bad-identity-action` | `unsat` | Checked QF_UF/Alethe evidence rejects the isolated bad identity-action equality. |
| `bad-compatibility-rejected` | `unsat` | Exact finite replay rejects a malformed action table that violates `s.(s.01) = (s*s).01`. |
| `qf-uf-bad-action-compatibility` | `unsat` | Checked QF_UF/Alethe evidence rejects the isolated bad action-compatibility equality. |
| `general-group-action-theory-lean-horizon` | `not-run` | Names the Lean route for general group-action theorems. |

The finite replay rows are exact finite table rows. The QF_UF/Alethe rows are
separate proof-object checks for equality conflicts isolated from those table
replays. They are not claims about arbitrary groups or infinite actions.
