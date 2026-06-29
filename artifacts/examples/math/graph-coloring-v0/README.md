# Graph Coloring V0

This pack covers finite graph coloring as the first pure field-extension pack
for `graph_theory`. It uses tiny explicit graphs, exact coloring replay,
deterministic exhaustive search, and a resource-backed CNF proof regression for
one non-colorability check.

The examples are the graph/SAT shadow that will later map to Axeyum's Bool,
BV, and CNF routes:

- proper 3-coloring witness for a triangle;
- rejection of an invalid edge coloring;
- exhaustive proof that a triangle is not 2-colorable;
- DIMACS CNF proof route for triangle non-2-colorability.

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
space for the `K3` two-colorability refutation. The CNF artifact
[`cnf/triangle-not-2-colorable.cnf`](cnf/triangle-not-2-colorable.cnf) encodes
the same two-colorability refutation as Boolean clauses. The focused CNF test
parses that artifact, emits a DRAT proof with Axeyum's proof-producing SAT core,
elaborates it to LRAT, and checks both proof objects independently.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes graph_coloring_triangle_not_2_colorable_emits_checked_drat_and_lrat
```
