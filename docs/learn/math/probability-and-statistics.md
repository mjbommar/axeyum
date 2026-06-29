# Probability And Statistics

Concept rows:

- `field_probability_theory`, `field_statistics`, and `field_measure_theory`
  in the [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_counting` and `curriculum_rationals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

Example packs:

- [finite-probability-v0](../../../artifacts/examples/math/finite-probability-v0/)
- [finite-integration-v0](../../../artifacts/examples/math/finite-integration-v0/)
- [finite-product-measure-v0](../../../artifacts/examples/math/finite-product-measure-v0/)
- [finite-markov-chain-v0](../../../artifacts/examples/math/finite-markov-chain-v0/)
- [descriptive-statistics-v0](../../../artifacts/examples/math/descriptive-statistics-v0/)
- [exact-statistical-tests-v0](../../../artifacts/examples/math/exact-statistical-tests-v0/)
- [finite-measure-v0](../../../artifacts/examples/math/finite-measure-v0/)
- [graph-d-separation-v0](../../../artifacts/examples/math/graph-d-separation-v0/)
- [random-matrix-finite-v0](../../../artifacts/examples/math/random-matrix-finite-v0/)

## What Axeyum Checks

The statistics path is exact and finite. It checks probability mass tables,
conditional probability, Bayes replay, finite sigma-algebra axioms, finite
additivity, event complements, finite simple-function integrals, indicator
integrals, finite product-measure tables, rectangle probabilities, marginals,
finite Fubini sums, exact mean/variance identities, contingency table margins,
and a Simpson's paradox count-table witness. The d-separation pack adds a
finite DAG bridge: it checks whether conditioning blocks or opens paths in
small causal-graph-shaped examples. The random-matrix pack checks
finite matrix-valued probability tables, exact moments, expected Gram matrices,
and rank probabilities. The Markov-chain pack checks exact stochastic matrices,
finite-horizon distribution evolution, stationary distributions, and malformed
transition rows.
The exact-test pack checks finite binomial tails, hypergeometric point
probabilities, and one-sided Fisher p-values as rational finite sums.

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
finite integration, it checks exact weighted sums such as:

```text
P(low) = 1/4
P(mid) = 1/4
P(high) = 1/2
f(low), f(mid), f(high) = 0, 2, 4
integral f dP = 5/2
```

The `finite-integration-v0` validator recomputes the simple-function integral,
indicator integrals, linear combinations, and a bad expectation counterexample.
For product measures, the validator checks a fair coin crossed with a fair
three-sided die:

```text
R(heads, one) = P(heads) * Q(one) = (1/2) * (1/3) = 1/6
R({heads} x {two, three}) = 1/3
sum_(x,y) f(x,y) R(x,y) = sum_x P(x) * sum_y f(x,y) Q(y) = 3
```

For descriptive statistics, it recomputes the mean and population variance of
`1,2,3,4`, then checks the reported margins of a finite contingency table.
For DAG examples, the validator enumerates simple skeleton paths and applies
the collider/non-collider conditioning rules. For random matrices, it
recomputes weighted trace, determinant, Gram, and rank claims from exact
matrix-valued atoms. For Markov chains, it applies exact row-vector transition
multiplication and checks stationarity by `pi * P = pi`.
For exact tests, it recomputes binomial coefficients and fixed-margin
hypergeometric sums directly.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-probability-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-integration-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-product-measure-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-markov-chain-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/descriptive-statistics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/exact-statistical-tests-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-measure-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-d-separation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/random-matrix-finite-v0
```

For a fuller trace through atom-table replay, read
[End To End: Conditional Probability, Product Measures, And Finite Expectation](finite-probability-end-to-end.md).

## Horizon

Continuous distributions, stochastic processes, convergence theorems, random
matrix spectral laws, concentration bounds, Lebesgue integration, monotone and
dominated convergence, general product measures, Fubini/Tonelli, MCMC, HMC,
variational inference, asymptotic statistical tests, calibration, causal
identification, do-calculus, and floating-point
diagnostics are not proof claims. They need either Lean-backed
probability/measure formalization or explicit reproducibility metadata with
seeds and tolerances.
