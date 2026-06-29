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

## Encode / Check Walkthrough

For a SAT witness, encode Boolean choices directly. The `PHP(2,2)` control case
uses variables like:

```text
x_p0_h0 = true
x_p0_h1 = false
x_p1_h0 = false
x_p1_h1 = true
```

The validator checks that every pigeon chooses one hole and no hole receives
two pigeons. For the `PHP(3,2)` UNSAT row, the pack deliberately records the
missing certificate route as a proof gap. That distinction is part of the
lesson: a replayed model and a checked UNSAT proof are different artifacts.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-refutation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
```

## Horizon

General first-order reasoning, induction-heavy metatheory, and proof assistant
automation need Lean or another kernel-checked route. For UNSAT examples, the
resource is not done until the certificate route is named and checked or the
proof gap stays explicit.
