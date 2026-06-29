# Finite Cardinality V0

This pack covers the first finite-cardinality slice for `cardinality`:
explicit bijections, finite cardinal inequalities, bounded injection/surjection
refutations, and an honest Lean horizon for infinite cardinality.

The examples are exact finite artifacts:

- replay a bijection between two three-element sets;
- replay a proper-subset injection from a two-element set into a three-element
  set;
- reject an injection from four elements into three elements by enumeration;
- reject a surjection from two elements onto three elements by enumeration;
- record Cantor-style infinite cardinality as a Lean-horizon theorem, not a
  solver result.

These checks do not claim countability, uncountability, Schroeder-Bernstein, or
cardinal arithmetic over infinite sets.

## Concepts

- `curriculum_cardinality`
- `curriculum_relations_and_functions`
- `curriculum_counting`
- `field_set_theory_and_foundations`
- `field_discrete_math`

## Trust Story

The validator recomputes every finite witness from the explicit function graph.
UNSAT rows are accepted only after enumerating the fixed finite function spaces
named in `expected.json`.

The infinite theorem row is metadata only: it must remain `lean-horizon` until a
real Lean module and checker command exist.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cardinality-v0
```
