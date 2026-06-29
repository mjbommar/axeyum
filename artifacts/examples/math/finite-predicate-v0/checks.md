# Checks

| ID | Expected | Trust Status | Route |
|---|---|---|---|
| `forall-predicate-finite-replay` | `sat` | checked | Replay a predicate table where all entries are true. |
| `exists-predicate-finite-replay` | `sat` | checked | Replay an existential witness element whose predicate value is true. |
| `forall-implies-exists-finite` | `unsat` | checked | Enumerate all unary predicates over a non-empty finite universe and find no counterexample. |
| `exists-not-forall-counterexample` | `sat` | checked | Replay one true witness and one false counterexample element. |
| `binary-relation-symmetry-counterexample` | `sat` | checked | Replay a binary predicate containing one pair but not its reverse. |
| `general-first-order-lean-horizon` | `not-run` | lean-horizon | Keep arbitrary-domain first-order validity out of the finite replay claim. |

The finite rows are deliberately small so the trusted checker can be inspected.
The pack does not claim a general theorem unless the row says `lean-horizon`.
