# Graph Coloring V0

This pack covers finite graph coloring as the first pure field-extension pack
for `graph_theory`. It uses tiny explicit graphs, exact coloring replay, and
deterministic exhaustive search for one non-colorability check.

The examples are the graph/SAT shadow that will later map to Axeyum's Bool,
BV, and CNF routes:

- proper 3-coloring witness for a triangle;
- rejection of an invalid edge coloring;
- exhaustive proof that a triangle is not 2-colorable.

## Concepts

- `field_graph_theory`
- `field_discrete_math`
- `field_logic_and_proof`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_counting`
- `curriculum_propositional_logic`

## Trust Story

The current validator checks graph data structurally, replays listed color
assignments against every edge, and exhaustively enumerates the finite color
space for the `K3` two-colorability refutation. It does not yet emit SAT/CNF,
call Axeyum's bit-blast-to-SAT route, or check LRAT/DRAT certificates for the
non-colorability claim.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
```
