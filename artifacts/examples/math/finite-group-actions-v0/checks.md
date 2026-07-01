# Checks

| Check | Result | Evidence |
|---|---|---|
| `c2-swap-action-laws` | `sat` | Check identity action and action compatibility over all table entries. |
| `orbit-stabilizer-replay` | `sat` | Recompute the orbit and stabilizer of `01`, then check `|orbit|*|stabilizer|=|G|`. |
| `burnside-orbit-count-replay` | `sat` | Recompute fixed-point counts for `e` and `s`, then check the Burnside average. |
| `bad-action-rejected` | `unsat` | Reject a malformed action table that violates the identity action, with checked QF_UF/Alethe evidence for the bad identity row. |
| `bad-compatibility-rejected` | `unsat` | Reject a malformed action table that violates `s.(s.01) = (s*s).01`, with checked QF_UF/Alethe evidence for the bad compatibility row. |
| `general-group-action-theory-lean-horizon` | `not-run` | Names the Lean route for general group-action theorems. |

The checked rows are exact finite table rows. They are not claims about
arbitrary groups or infinite actions.
