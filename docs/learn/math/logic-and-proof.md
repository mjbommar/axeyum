# Logic And Proof

Concept rows:

- `curriculum_proof_methods`, `curriculum_propositional_logic`, and
  `field_logic_and_proof` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `proof-methods` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

Example packs:

- [proof-methods-refutation-v0](../../../artifacts/examples/math/proof-methods-refutation-v0/)
- [graph-coloring-v0](../../../artifacts/examples/math/graph-coloring-v0/)

## What Axeyum Checks

The first proof lesson is refutation: negate the claim, ask whether the negation
has a model, then replay the result. The proof-methods pack records a small
pigeonhole SAT witness and an UNSAT pigeonhole claim with an explicit proof gap.
The graph-coloring pack adds a finite non-colorability example that can be
exhaustively checked.

## Horizon

General first-order reasoning, induction-heavy metatheory, and proof assistant
automation need Lean or another kernel-checked route. For UNSAT examples, the
resource is not done until the certificate route is named and checked or the
proof gap stays explicit.
