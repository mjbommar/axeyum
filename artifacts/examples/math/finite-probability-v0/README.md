# Finite Probability V0

This pack covers exact finite probability tables for the `probability_theory`
field-extension row. It uses finite outcome spaces and rational arithmetic, not
floating point and not sampling.

The examples are the finite probability shadow that maps satisfiable tables to
replay today and future invalid probability constraints to Axeyum's LRA
certificate route:

- probability mass table sums to one;
- impossible normalization rejected with checked QF_LRA/Farkas evidence;
- conditional probability replay from an atom table;
- Bayes posterior replay for a small diagnostic-test table.

## Concepts

- `field_probability_theory`
- `field_statistics`
- `field_measure_theory`
- `curriculum_counting`
- `curriculum_rationals`
- `curriculum_sets`

## Trust Story

The current validator parses probabilities exactly as rational strings, checks
that mass tables are normalized and nonnegative, and recomputes conditional and
Bayes probabilities. Satisfiable finite-table rows remain finite-model replay.
The bad normalization row is a small `QF_LRA` contradiction and must emit
checked `UnsatFarkas` evidence. Future impossible nonnegativity, conditioning,
or Bayes-rule constraints should use the same QF_LRA/Farkas route.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-probability-v0
```
