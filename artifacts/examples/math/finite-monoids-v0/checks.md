# Checks

| Check | Result | Evidence |
|---|---|---|
| `two-point-transformation-monoid-laws` | `sat` | Check identity and associativity over the listed composition table. |
| `function-composition-table-replay` | `sat` | Recompute every table entry from the finite function maps. |
| `units-and-idempotents-replay` | `sat` | Recompute invertible elements and idempotents from the monoid table. |
| `bad-nonassociative-table-rejected` | `unsat` | Reject a table with an identity but a concrete associativity failure. |
| `general-monoid-theory-lean-horizon` | `not-run` | Names the Lean route for general semigroup and monoid theorems. |

The checked rows are exact finite table rows. They are not claims about
arbitrary monoids, free monoids, or infinite transformation semigroups.
