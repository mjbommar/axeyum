# Proof Methods Refutation V0

This pack turns proof by contradiction into a concrete solver workflow:

```text
claim is valid  <=>  negation of claim is UNSAT
```

The worked example is the finite pigeonhole principle. Three pigeons cannot be
placed into two holes if every pigeon must occupy exactly one hole and each hole
can hold at most one pigeon.

## Concepts

- `curriculum_proof_methods`
- `curriculum_propositional_logic`
- `curriculum_counting`

## Trust Story

- SAT witness replay is checked for the smaller `PHP(2,2)` control case.
- The main `PHP(3,2)` UNSAT result is checked against a deterministic CNF by
  exhaustive finite truth-table enumeration.
- LRAT/DRAT remains a stronger graduation route; this pack does not claim a
  proof object until such an artifact is emitted and checked.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-refutation-v0
```
