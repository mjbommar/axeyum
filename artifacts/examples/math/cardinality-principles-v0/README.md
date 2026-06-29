# Cardinality Principles V0

This pack deepens the `cardinality` curriculum node with finite counting
principles that show up across set theory, discrete math, probability, and
proof methods.

The examples are:

- inclusion-exclusion for two finite sets;
- disjoint-union additivity;
- double-counting the edges of a finite bipartite graph;
- powerset cardinality for a three-element set;
- a checked counterexample to the false rule `|A union B| = |A| + |B|` when
  the sets overlap;
- a Lean-horizon row for arbitrary infinite cardinality theorems.

## Concepts

- `curriculum_cardinality`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_counting`
- `field_set_theory_and_foundations`
- `field_discrete_math`

## Trust Story

The validator replays every finite count from the listed sets, subsets,
function-like incidence tables, and degree tables. Counterexample rows are
accepted only when the listed finite data really violates the false rule.

These checks are finite arithmetic evidence. They do not prove arbitrary
cardinal arithmetic, Cantor-Schroeder-Bernstein, countability, or choice
principles. Those remain Lean-horizon rows until kernel-checked artifacts exist.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/cardinality-principles-v0
```
