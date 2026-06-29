# Logic And Proof

Concept rows:

- `curriculum_proof_methods`, `curriculum_propositional_logic`,
  `curriculum_induction`, and `field_logic_and_proof` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `proof-methods` and `induction` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

Example packs:

- [logic-basics-v0](../../../artifacts/examples/math/logic-basics-v0/)
- [proof-methods-refutation-v0](../../../artifacts/examples/math/proof-methods-refutation-v0/)
- [induction-obligations-v0](../../../artifacts/examples/math/induction-obligations-v0/)
- [graph-coloring-v0](../../../artifacts/examples/math/graph-coloring-v0/)

## What Axeyum Checks

The first proof lesson is Boolean: replay a SAT witness, negate a tautology and
check no counterexample exists, and enumerate tiny CNF rows. The proof-methods
pack records a small pigeonhole SAT witness and an UNSAT pigeonhole claim with
an explicit proof gap. The induction pack checks bounded base, step, and
conclusion obligations while keeping the full induction schema under Lean
horizon. The graph-coloring pack adds a finite non-colorability example that can
be exhaustively checked.

## Encode / Check Walkthrough

For propositional logic, encode Boolean assignments and formulas directly:

```text
p = true
q = true
formula = p and q
```

The `logic-basics-v0` validator replays that witness, enumerates truth tables
for excluded middle, contradiction, and De Morgan equivalence, and checks a tiny
CNF refutation by enumeration. For a SAT witness in a domain example, encode
Boolean choices directly. The `PHP(2,2)` control case uses variables like:

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
For induction, encode the finite obligations for a specific property:

```text
P(n): 0 + 1 + ... + n = n * (n + 1) / 2
base: P(0)
step: P(k) -> P(k + 1), for k <= 8
```

The validator replays the base case, enumerates bounded step and conclusion
counterexamples, and keeps the full `for all n` induction schema as a
Lean-horizon row.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/logic-basics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-refutation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/induction-obligations-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
```

## Horizon

General first-order reasoning, the universal induction schema, and proof
assistant automation need Lean or another kernel-checked route. For UNSAT
examples, the resource is not done until the certificate route is named and
checked or the proof gap stays explicit.
