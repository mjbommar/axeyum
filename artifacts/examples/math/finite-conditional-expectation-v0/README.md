# Finite Conditional Expectation V0

This pack adds exact finite conditional-expectation checks. It treats a
conditioning sigma-algebra as a finite partition of probability atoms and
checks that conditional expectations are blockwise weighted averages.

The examples are:

- a conditional-expectation-by-partition witness;
- a law-of-total-expectation witness;
- a finite tower-property witness over nested partitions;
- checked QF_LRA/Farkas rejection of a false conditional expectation table;
- checked QF_LRA/Farkas rejection of a false tower-property table;
- a general conditional-expectation and martingale Lean-horizon row.

## Concepts

- `field_probability_theory`
- `field_statistics`
- `field_measure_theory`
- `field_real_analysis`
- `field_set_theory_and_foundations`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_rationals`
- `curriculum_counting`

## Trust Story

The validator checks normalized finite atom probabilities, verifies that each
conditioning family is a partition of the atom set, recomputes every blockwise
conditional average with exact rational arithmetic, checks the law of total
expectation, and checks the finite tower property for nested partitions.

This pack is checked finite evidence for the bad conditional-expectation and
bad tower-property rows. The false high-block and false tower tables are routed
through Axeyum's checked `UnsatFarkas` evidence path. It is not a proof of
general conditional expectation, Radon-Nikodym construction, martingales,
stopping times, or regular conditional probabilities.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-conditional-expectation-v0
```
