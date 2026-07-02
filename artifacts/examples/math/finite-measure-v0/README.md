# Finite Measure V0

This pack covers tiny finite measure examples for the `measure_theory`
field-extension row. It uses explicit finite sigma-algebras and exact rational
measures, not Lebesgue measure, integration, or convergence theorems.

The examples are the finite measure shadow that will later map to Axeyum's
finite-set and LRA routes:

- finite sigma-algebra axiom replay;
- finite measure normalization and finite additivity;
- event/complement probability replay;
- exact replay rejection of a malformed complement-measure row;
- a checked QF_LRA/Farkas rejection of the isolated complement-additivity
  contradiction.

## Concepts

- `field_measure_theory`
- `field_probability_theory`
- `field_set_theory_and_foundations`
- `curriculum_sets`
- `curriculum_rationals`
- `curriculum_counting`

## Trust Story

The current validator checks the sigma-algebra by explicit finite set
computation: empty/universe membership, complement closure, and pairwise union
closure. It parses all measures exactly as rational strings and checks
nonnegativity, `mu(empty) = 0`, normalization, and finite additivity for
disjoint measurable sets. The bad-complement replay row computes the event,
complement, and total measures; the separate checked QF_LRA/Farkas row checks
only the final exact-linear contradiction. It does not claim anything about
countable additivity or infinite measure spaces.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-measure-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_measure_bad_complement_artifact_emits_checked_farkas
```
