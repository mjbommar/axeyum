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
- impossible conditional probability rejected with checked QF_LRA/Farkas evidence;
- Bayes posterior replay for a small diagnostic-test table;
- impossible Bayes posterior rejected with checked QF_LRA/Farkas evidence;
- finite independence replay for a four-atom table;
- impossible independence joint mass rejected with checked QF_LRA/Farkas
  evidence;
- total variation replay for two three-atom distributions;
- impossible total variation distance rejected with checked QF_LRA/Farkas
  evidence.

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
The bad normalization, bad conditional probability, bad Bayes posterior, bad
independence, and bad total-variation rows are small `QF_LRA` contradictions
and must emit checked `UnsatFarkas` evidence. Future impossible nonnegativity
or finite probability-table distance constraints should use the same
QF_LRA/Farkas route.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-probability-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_probability_bad_total_variation_artifact_emits_checked_farkas
```
