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

## Encode / Check Walkthrough

For finite probability, encode atoms with exact rational mass. In the
conditional-probability witness:

```text
P(rain and late) = 1/10
P(rain and on_time) = 1/5
P(late | rain) = (1/10) / (1/10 + 1/5) = 1/3
```

The validator recomputes the numerator, denominator, and quotient. For
descriptive statistics, it recomputes the mean and population variance of
`1,2,3,4`, then checks the reported margins of a finite contingency table.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-probability-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/descriptive-statistics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-measure-v0
```

For a fuller trace through atom-table replay, read
[End To End: Conditional Probability](finite-probability-end-to-end.md).

## Horizon

Continuous distributions, stochastic processes, convergence theorems, MCMC,
HMC, variational inference, calibration, and floating-point diagnostics are not
proof claims. They need either Lean-backed probability/measure formalization or
explicit reproducibility metadata with seeds and tolerances.
