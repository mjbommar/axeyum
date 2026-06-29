# Probability And Statistics

Concept rows:

- `field_probability_theory`, `field_statistics`, and `field_measure_theory`
  in the [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_counting` and `curriculum_rationals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

Example packs:

- [finite-probability-v0](../../../artifacts/examples/math/finite-probability-v0/)
- [descriptive-statistics-v0](../../../artifacts/examples/math/descriptive-statistics-v0/)
- [finite-measure-v0](../../../artifacts/examples/math/finite-measure-v0/)

## What Axeyum Checks

The statistics path is exact and finite. It checks probability mass tables,
conditional probability, Bayes replay, finite sigma-algebra axioms, finite
additivity, event complements, exact mean/variance identities, contingency
table margins, and a Simpson's paradox count-table witness.

The trusted checker works over rational arithmetic and finite tables.

## Horizon

Continuous distributions, stochastic processes, convergence theorems, MCMC,
HMC, variational inference, calibration, and floating-point diagnostics are not
proof claims. They need either Lean-backed probability/measure formalization or
explicit reproducibility metadata with seeds and tolerances.
