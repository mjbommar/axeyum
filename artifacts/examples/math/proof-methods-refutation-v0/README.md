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
- The Boolean route regression parses
  [`cnf/php-3-2.cnf`](cnf/php-3-2.cnf), emits a DRAT refutation, elaborates it
  to LRAT, and checks both proof objects.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-refutation-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes proof_methods_refutation_php_3_2_emits_checked_drat_and_lrat
```
