# Relations And Functions V0

This pack covers the next core curriculum slice after finite sets: relations as
sets of ordered pairs, functions as single-valued total relations, and finite
table checks for order and bijection properties.

The examples are the finite-domain shadow of Axeyum's Bool/BV and EUF routes:

- replay a partial-order relation over a three-element finite universe;
- replay a bijective function table between two finite sets;
- reject a malformed function graph with two outputs for one input.

These checks are intentionally finite. They do not claim general function
theory, choice principles, or infinite-domain cardinality facts. They create the
small table discipline needed by later packs for cardinality, finite algebra,
linear maps, recurrences, and EUF congruence examples.

## Concepts

- `curriculum_relations_and_functions`
- `curriculum_sets`
- `field_set_theory_and_foundations`
- `field_discrete_math`

## Trust Story

The validator checks that relation pairs live over their declared carrier sets,
then recomputes reflexivity, antisymmetry, transitivity, totality,
single-valuedness, injectivity, and surjectivity directly. Satisfiable rows are
accepted only after replaying the listed finite table. The malformed function
row is accepted only because the validator confirms the fixed table violates
single-valuedness.

This pack does not yet emit Axeyum EUF terms or checked Alethe evidence. The
QF_UF congruence route is linked as the graduation target once a future pack
adds explicit congruence-conflict artifacts.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/relations-functions-v0
```
