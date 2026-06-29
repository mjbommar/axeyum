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

- SAT witness replay is represented for the smaller `PHP(2,2)` control case.
- The main `PHP(3,2)` UNSAT result is intentionally marked as a proof gap until
  the pack has a CNF/LRAT emission and checker route.
- This is an example-pack scaffold for the trusted-small-checking lesson, not a
  claim that the proof certificate has landed.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-refutation-v0
```
