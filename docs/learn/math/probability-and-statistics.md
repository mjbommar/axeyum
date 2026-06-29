# Probability And Statistics

Concept rows:

- `field_probability_theory`, `field_statistics`, and `field_measure_theory`
  in the [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_counting` and `curriculum_rationals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

Example packs:

- [finite-probability-v0](../../../artifacts/examples/math/finite-probability-v0/)
- [finite-random-variables-v0](../../../artifacts/examples/math/finite-random-variables-v0/)
- [finite-conditional-expectation-v0](../../../artifacts/examples/math/finite-conditional-expectation-v0/)
- [finite-stochastic-kernels-v0](../../../artifacts/examples/math/finite-stochastic-kernels-v0/)
- [finite-hitting-times-v0](../../../artifacts/examples/math/finite-hitting-times-v0/)
- [finite-martingales-v0](../../../artifacts/examples/math/finite-martingales-v0/)
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
integrals, finite random-variable pushforwards, expectations through
pushforward distributions, independence checks, finite partition conditional
expectations, the law of total expectation, tower property replay, finite
stochastic-kernel normalization, pushforward, joint disintegration, kernel
composition, finite first-hit distributions, survival probabilities,
absorption-probability equations, expected hitting-time equations, finite
filtrations, martingale conditional-expectation equalities, square
submartingale inequalities, bounded stopping-time replay, finite product-measure
tables, rectangle probabilities, marginals, finite Fubini sums, exact
mean/variance identities, contingency table margins, and a Simpson's paradox
count-table witness. The d-separation pack adds a finite DAG bridge:
it checks whether conditioning blocks or opens paths in small
causal-graph-shaped examples. The random-matrix pack checks
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

The validator recomputes the numerator, denominator, and quotient. For finite
random variables, it checks pushforwards and expectations such as:

```text
P(clear) = 1/2, P(rain) = 1/4, P(storm) = 1/4
X(clear), X(rain), X(storm) = short, medium, long
P(X = long) = 1/4
E[X] = 20
```

The `finite-random-variables-v0` validator recomputes the pushforward mass,
expectation from source atoms, expectation from the pushforward distribution,
and finite independence of two random variables over a four-atom table.
Conditional expectation checks partition averages such as:

```text
P(a) = P(b) = P(c) = P(d) = 1/4
X(a), X(b), X(c), X(d) = 0, 2, 4, 8
partition = {a,b}, {c,d}
E[X | {a,b}] = 1
E[X | {c,d}] = 6
```

The `finite-conditional-expectation-v0` validator recomputes block averages,
`E[E[X|G]] = E[X]`, and a finite tower-property row for nested partitions.
Finite kernels check conditional distributions as source-to-target tables:

```text
K(sunny, walk) = 3/4
K(sunny, bus) = 1/4
K(rainy, walk) = 1/5
K(rainy, bus) = 4/5
mu(sunny), mu(rainy) = 2/3, 1/3
nu(walk) = 2/3*3/4 + 1/3*1/5 = 17/30
```

The `finite-stochastic-kernels-v0` validator checks row normalization,
pushforward distributions, joint-table factorization and disintegration, and
kernel composition.
For finite hitting times in an absorbing Markov chain, it checks:

```text
P(T = 1) = 0
P(T = 2) = 1/4
P(T = 3) = 1/4
P(T = 4) = 3/16
P(T > 4) = 5/16
h(start) = 4
h(middle) = 2
h(hit) = 0
```

The `finite-hitting-times-v0` validator carries only not-yet-hit mass forward,
checks the survival mass, and verifies the absorption-probability and expected
hitting-time linear equations.
For finite martingales, it checks a two-step fair walk against its natural
filtration:

```text
M0 = 0
M1(up) = 1, M1(down) = -1
M2(uu), M2(ud), M2(du), M2(dd) = 2, 0, 0, -2
E(M2 | F1, up) = 1
E(M2 | F1, down) = -1
```

The `finite-martingales-v0` validator checks adaptedness, recomputes each
martingale equality, checks the square submartingale inequalities, and replays
a bounded stopping time by exact expectation.
For finite integration, it checks exact weighted sums such as:

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
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-random-variables-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-conditional-expectation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-stochastic-kernels-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-hitting-times-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-martingales-v0
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
[End To End: Conditional Probability, Random Variables, Kernels, Martingales, And Product Measures](finite-probability-end-to-end.md).

## Horizon

Continuous distributions, stochastic processes, convergence theorems, random
matrix spectral laws, concentration bounds, Lebesgue integration, monotone and
dominated convergence, general product measures, Fubini/Tonelli, conditional
expectation, regular conditional probabilities, disintegration theorems,
general Markov kernels, recurrence/transience classifications,
infinite-horizon hitting probabilities, general martingale convergence,
optional stopping, Doob inequalities, MCMC, HMC, variational inference,
asymptotic statistical tests, calibration, causal identification, do-calculus,
and floating-point diagnostics are not proof claims. They need either
Lean-backed probability/measure formalization or explicit reproducibility
metadata with seeds and tolerances.
