# Retrieved-induction type-slice replay

Date: 2026-08-26

## Result

All 25 positive targets that the retrieved-induction census rejected at
ordinary statement import now pass the existing checked type-slice boundary.
For each exact current capsule, the replay:

1. imports and checks the complete source stream;
2. selects proof-bearing implementation constants for abstraction;
3. constructs a closed generalized proposition;
4. root-exports only that proposition into a fresh stream;
5. imports it through the proof-isolated statement boundary; and
6. checks that applying the exact source constants recovers the original
   proposition definitionally.

The result contains 25 accepted receipts, zero declines, zero proof producer
executions, zero held-out access, and zero ledger writes. Three receipts use
checked `autoParam` normalization. Every fresh environment retains only
definitions, inductives, constructors, and recursors—never an axiom, theorem,
opaque declaration, or quotient primitive.

The committed
[`input`](../../artifacts/autogenesis/retrieved-induction-type-slice-input-v1.json)
and
[`replay`](../../artifacts/autogenesis/retrieved-induction-type-slice-replay-v1.json)
make the evaluation dependency explicit. These rows were selected because a
prior producer run observed their import failures; they are not a blind
baseline. The observation records `target_outcomes_accessed: true` and cannot
be confused with the historical frozen 138-row replay, whose contract still
requires that value to be false.

## What the boundary exposed

Safe presentation is no longer the blocker for these 25 rows. It is also not a
proof. Every accepted slice abstracts one to three exact source definitions:

| Abstracted source family | Target occurrences |
|---|---:|
| `Int.fib` | 4 |
| `Nat.instAndOp`, `Nat.instOrOp`, `Nat.testBit` | 4 each |
| `Nat.instPreorder`, `Nat.multichoose` | 3 each |
| `Nat.Coprime`, `Nat.ldiff` | 2 each |
| `Int.gcd`, `Int.gcdA`, `Int.gcdB`, `List.getI`, `Nat.bits`, `Nat.fastFib` | 1 each |

There are 14 distinct abstraction identities. Generalizing one of them turns a
claim about a concrete operation into a stronger claim about an arbitrary
function or instance. A producer therefore needs independently checked
behavior contracts—recurrence equations, bit semantics, order laws, or exact
specialization bridges—before the retrieved native lemmas can apply to the
generalized symbol. Merely running the equality grammar on the stronger goal
would measure a known missing premise, not autonomous reasoning.

## Next sequence

1. Generate a semantic-contract demand graph from these receipts, grouping
   targets by exact abstraction identity and visible proposition shape.
2. Link each group to existing axiom-free kernel equations and existing
   semantic-contract receipts by exact declaration identity; leave unmatched
   demands explicit.
3. Choose the largest family with reusable checked contracts, attach those
   contracts to the sliced producer environment, and rerun all siblings under
   one unchanged grammar.
4. Only if at least three previously open siblings convert should the producer
   contract advance toward operation registration and a clean transaction.

Run the repository-only freshness gate with
`just autogenesis-retrieved-induction-type-slice`. On a host with the external
capsules mounted, reproduce all checks—including source byte hashes—with
`just autogenesis-retrieved-induction-type-slice-reproduce`.
