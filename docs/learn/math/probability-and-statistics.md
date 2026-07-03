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
- [finite-concentration-v0](../../../artifacts/examples/math/finite-concentration-v0/)
- [finite-martingales-v0](../../../artifacts/examples/math/finite-martingales-v0/)
- [finite-integration-v0](../../../artifacts/examples/math/finite-integration-v0/)
- [finite-product-measure-v0](../../../artifacts/examples/math/finite-product-measure-v0/)
- [finite-markov-chain-v0](../../../artifacts/examples/math/finite-markov-chain-v0/)
- [descriptive-statistics-v0](../../../artifacts/examples/math/descriptive-statistics-v0/)
- [finite-covariance-matrix-v0](../../../artifacts/examples/math/finite-covariance-matrix-v0/)
- [finite-principal-components-v0](../../../artifacts/examples/math/finite-principal-components-v0/)
- [finite-k-means-clustering-v0](../../../artifacts/examples/math/finite-k-means-clustering-v0/)
- [least-squares-regression-v0](../../../artifacts/examples/math/least-squares-regression-v0/)
- [finite-linear-discriminant-v0](../../../artifacts/examples/math/finite-linear-discriminant-v0/)
- [exact-statistical-tests-v0](../../../artifacts/examples/math/exact-statistical-tests-v0/)
- [finite-measure-v0](../../../artifacts/examples/math/finite-measure-v0/)
- [finite-measure-monotonicity-v0](../../../artifacts/examples/math/finite-measure-monotonicity-v0/)
- [graph-d-separation-v0](../../../artifacts/examples/math/graph-d-separation-v0/)
- [random-matrix-finite-v0](../../../artifacts/examples/math/random-matrix-finite-v0/)

Companion map:

- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)
- [Random Variable Theorem Boundary](random-variable-theorem-boundary.md)
- [Stochastic Kernel Theorem Boundary](stochastic-kernel-theorem-boundary.md)
- [Hitting-Time Theorem Boundary](hitting-time-theorem-boundary.md)
- [Martingale Theorem Boundary](martingale-theorem-boundary.md)
- [Concentration Theorem Boundary](concentration-theorem-boundary.md)
- [Lebesgue Integration Theorem Boundary](lebesgue-integration-theorem-boundary.md)
- [Fubini Tonelli Theorem Boundary](fubini-tonelli-theorem-boundary.md)

## What Axeyum Checks

The statistics path is exact and finite. It checks probability mass tables,
conditional probability, Bayes replay, finite sigma-algebra axioms, finite
additivity, event complements, finite measure monotonicity, finite union
subadditivity, exact bad-complement replay with a separate checked QF_LRA
bad-complement certificate, a checked QF_LRA
bad subset-measure certificate, a checked QF_LRA bad union-subadditivity
certificate, checked QF_LRA bad-normalization,
bad-conditional-probability, bad-Bayes, bad-independence, and
bad-total-variation certificates,
finite simple-function integrals, indicator
integrals, finite random-variable pushforwards, expectations through
pushforward distributions, independence checks, a checked QF_LRA bad
expectation-through-pushforward certificate, finite partition conditional
expectations, the law of total expectation, tower property replay, checked
QF_LRA bad high-block, bad total-expectation, bad tower-property, and bad
variance-decomposition certificates, finite
stochastic-kernel normalization, pushforward, joint disintegration, kernel
composition, finite first-hit distributions, survival probabilities,
absorption-probability equations, expected hitting-time equations, finite
concentration/tail-bound replays, finite filtrations, martingale
conditional-expectation equalities, square submartingale inequalities, bounded
stopping-time replay, finite product-measure tables, rectangle probabilities,
marginals, finite Fubini sums, exact
mean/variance identities, exact bad-variance replay with a separate checked
QF_LRA bad-variance certificate,
finite covariance-matrix replay over exact rational sample rows, centered
Gram matrices, positive-semidefinite shadows, and a checked QF_LRA
bad-covariance-entry certificate,
finite principal-component covariance/eigenpair replay, projected scores,
one-component residual energy, explained-variance ratio, and checked QF_LRA
bad-principal-eigenvalue evidence,
finite k-means assigned-cluster replay, exact centroids, residuals, WCSS,
total/between scatter decomposition, replayed bad-centroid rejection, and
checked QF_LRA bad-centroid evidence,
contingency table margins, a checked QF_LIA bad contingency-total certificate,
least-squares normal equations, checked QF_LRA bad-RSS and bad-coefficients
certificates, finite linear-discriminant class means, within-class scatter,
Fisher direction, projected training scores, threshold margins, and checked
QF_LRA bad-direction evidence, and a Simpson's paradox count-table witness.
The d-separation pack adds a finite DAG bridge:
it checks whether conditioning blocks or opens paths in small
causal-graph-shaped examples. The random-matrix pack checks
finite matrix-valued probability tables, exact moments, expected Gram matrices,
rank probabilities, and checked QF_LRA/Farkas rejections of bad trace-square
and expected-rank claims. The Markov-chain pack checks exact stochastic matrices,
finite-horizon distribution evolution, stationary distributions, replayed bad
transition/stationary rows, and separate checked `UnsatFarkas` certificates for
the final scalar contradictions.

For a focused finite Markov-chain trace, read
[End To End: Finite Markov Chains](finite-markov-chain-end-to-end.md).
For a focused finite Bayes-update trace, read
[End To End: Finite Bayes Update](finite-bayes-update-end-to-end.md).
For a focused finite classification trace, read
[End To End: Finite Linear Discriminant](linear-discriminant-end-to-end.md).
For a focused finite PCA trace, read
[End To End: Finite Principal Components](principal-components-end-to-end.md).
For a focused finite clustering trace, read
[End To End: Finite K-Means Clustering](k-means-clustering-end-to-end.md).

The exact-test pack checks finite binomial tails, hypergeometric point
probabilities, one-sided and probability-ordered two-sided Fisher p-values as
rational finite sums, a probability-ordered exact multinomial p-value, checked
QF_LRA/Farkas certificates for rejected Fisher and multinomial p-value claims,
and a checked QF_LIA/Diophantine certificate for a rejected binomial
tail-count claim.

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
probability it also rejects a false normalization row, `1/2 + 1/2 = 3/2`, and
a false total-variation row where two three-atom distributions have replayed
distance `1/6` but the malformed claim asserts `1/4`, both with checked
`UnsatFarkas` evidence. For finite measure, the same route rejects a bad
complement row where `mu(A)=1/3`, `mu(U)=1`, and the malformed claim
requires `mu(A^c)=1/2` while preserving `mu(A)+mu(A^c)=mu(U)`.
The finite-measure monotonicity pack replays `A subset B` by computing
`B \ A`, checking `mu(B)=mu(A)+mu(B\A)`, and rejecting a false
`mu({a})=2/3` row after replay computes `mu({a})=1/6`.
For the diagnostic-test Bayes row, exact replay starts from:

```text
P(disease) = 1/100
P(positive | disease) = 9/10
P(positive | not disease) = 1/20
```

It recomputes `P(disease and positive)=9/1000`,
`P(positive)=117/2000`, and therefore
`P(disease | positive)=2/13`. The malformed Bayes row claims posterior `1/5`;
the checked `QF_LRA` artifact refutes the division-free equation:

```text
evidence_probability * posterior = disease_and_positive_probability
```

with the replayed source values. The focused trace is
[End To End: Finite Bayes Update](finite-bayes-update-end-to-end.md).
For finite random variables, it checks
pushforwards and expectations such as:

```text
P(clear) = 1/2, P(rain) = 1/4, P(storm) = 1/4
X(clear), X(rain), X(storm) = short, medium, long
P(X = long) = 1/4
E[X] = 20
```

The `finite-random-variables-v0` validator recomputes the pushforward mass,
expectation from source atoms, expectation from the pushforward distribution,
and finite independence of two random variables over a four-atom table. It
rejects the malformed expectation row `E[X] = 25` because both exact replay
routes compute `E[X] = 20`; the separate `qf-lra-*` rows check the final linear
pushforward and expectation conflicts through `UnsatFarkas`.

For a focused finite random-variable trace, read
[End To End: Finite Random Variables](finite-random-variables-end-to-end.md).
For the theorem boundary that keeps finite total-function, pushforward,
expectation, independence, and checked bad-row resources separate from
measurable-function, distribution-law, convergence, and continuous random
variable claims, read
[Random Variable Theorem Boundary](random-variable-theorem-boundary.md).
Conditional expectation checks partition averages such as:

```text
P(a) = P(b) = P(c) = P(d) = 1/4
X(a), X(b), X(c), X(d) = 0, 2, 4, 8
partition = {a,b}, {c,d}
E[X | {a,b}] = 1
E[X | {c,d}] = 6
```

The `finite-conditional-expectation-v0` validator recomputes block averages,
`E[E[X|G]] = E[X]`, a finite tower-property row for nested partitions, and a
finite conditional-variance decomposition, then checks Farkas certificates for
the bad high-block table, false total-expectation value, false tower value, and
false variance-decomposition total.
For the theorem boundary that keeps these finite partition averages,
total-expectation, tower, variance-decomposition, and checked bad-row resources
separate from Radon-Nikodym, general conditional-expectation,
regular-conditional-probability, and stopping-time claims, read
[Conditional Expectation Theorem Boundary](conditional-expectation-theorem-boundary.md).
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
kernel composition, including checked QF_LRA/Farkas rejection of malformed
row-normalization and composed-entry claims.

For a focused finite stochastic-kernel trace, read
[End To End: Finite Stochastic Kernels](finite-stochastic-kernels-end-to-end.md).
For the theorem boundary that keeps finite row normalization, pushforward,
joint-disintegration, composition, and checked bad-row resources separate from
regular conditional probability, disintegration, measurable-kernel, and
stochastic-process theorem claims, read
[Stochastic Kernel Theorem Boundary](stochastic-kernel-theorem-boundary.md).

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
hitting-time linear equations. Its bad survival-mass and bad expected-time rows
are replay-only; the separate `qf-lra-bad-survival-mass` and
`qf-lra-bad-expected-time` rows carry checked `UnsatFarkas` evidence for the
isolated scalar conflicts.

For a focused finite hitting-time trace, read
[End To End: Finite Hitting Times](finite-hitting-times-end-to-end.md).
For the theorem boundary that keeps these finite first-hit, survival-mass,
absorption-probability, and expected-time rows separate from recurrence,
transience, optional-stopping, mixing, and potential-theory claims, read
[Hitting-Time Theorem Boundary](hitting-time-theorem-boundary.md).

For finite concentration checks, it recomputes exact tail probabilities and
standard finite inequalities:

```text
P(low) = 3/4
P(high) = 1/4
X(low) = 0
X(high) = 4
P(X >= 2) = 1/4
E[X] / 2 = 1/2
```

The `finite-concentration-v0` validator checks Markov's inequality,
Chebyshev's inequality, the union bound, and rejects a false claim such as
`P(X >= 2) <= 1/8` for this table or `P(A union B) <= 1/2` when exact replay
computes `P(A union B) = 3/4`.

For a focused finite concentration trace, read
[End To End: Finite Concentration](finite-concentration-end-to-end.md). For
the theorem boundary that keeps these finite Markov, Chebyshev, and union-bound
rows separate from Chernoff, Hoeffding, martingale concentration, limit
theorems, and asymptotic statistics, read
[Concentration Theorem Boundary](concentration-theorem-boundary.md).

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
a bounded stopping time by exact expectation. Its bad stopped-expectation and
bad martingale rows are replay-only; the separate
`qf-lra-bad-stopped-expectation` and `qf-lra-bad-martingale` rows carry checked
`UnsatFarkas` evidence for the isolated scalar conflicts.

For a focused finite martingale trace, read
[End To End: Finite Martingales](finite-martingales-end-to-end.md).
For the theorem boundary that keeps these finite filtration,
submartingale, bounded-stopping, and checked bad-row resources separate from
martingale convergence, optional-stopping, Doob-inequality,
stochastic-integration, and continuous-time claims, read
[Martingale Theorem Boundary](martingale-theorem-boundary.md).

For finite integration, it checks exact weighted sums such as:

```text
P(low) = 1/4
P(mid) = 1/4
P(high) = 1/2
f(low), f(mid), f(high) = 0, 2, 4
integral f dP = 5/2
```

The `finite-integration-v0` validator recomputes the simple-function integral,
indicator integrals, linear combinations, and a bad expectation counterexample;
the separate `qf-lra-bad-expectation` row checks the final exact-linear
contradiction.
For product measures, the validator checks a fair coin crossed with a fair
three-sided die:

```text
R(heads, one) = P(heads) * Q(one) = (1/2) * (1/3) = 1/6
R({heads} x {two, three}) = 1/3
sum_(x,y) f(x,y) R(x,y) = sum_x P(x) * sum_y f(x,y) Q(y) = 3
```

For the theorem boundary that keeps finite product tables, marginals, and
finite iterated sums separate from product-measure construction,
Fubini/Tonelli, and almost-everywhere claims, read
[Fubini Tonelli Theorem Boundary](fubini-tonelli-theorem-boundary.md).

For descriptive statistics, it recomputes the mean and population variance of
`1,2,3,4`, checks the reported margins of a finite contingency table, rejects
a bad variance claim by exact replay, and emits a separate checked
`UnsatFarkas` certificate for the isolated variance equation plus a checked
`UnsatDiophantine` certificate for the bad total-count row.
For finite covariance, it recomputes the sample mean vector, centered rows,
centered Gram matrix, covariance matrix, and two-by-two
positive-semidefinite shadow, then emits checked `UnsatFarkas` evidence for
the malformed off-diagonal covariance entry.
For finite Naive Bayes classification, it recomputes exact class counts,
binary feature counts, Laplace-smoothed likelihoods, class scores, normalized
posterior probabilities, and the finite decision, then emits checked
`UnsatFarkas` evidence for a malformed posterior claim.
For finite classifier metrics, it recomputes exact actual/predicted row
counts, TP/FP/TN/FN, accuracy, precision, recall, specificity, negative
predictive value, false-positive/false-negative rates, balanced accuracy, F1,
and Jaccard, then emits checked `UnsatFarkas` evidence for a malformed
precision claim.
For DAG examples, the validator enumerates simple skeleton paths and applies
the collider/non-collider conditioning rules. For random matrices, it
recomputes weighted trace, determinant, Gram, and rank claims from exact
matrix-valued atoms. For Markov chains, it applies exact row-vector transition
multiplication, checks stationarity by `pi * P = pi`, and emits checked
`UnsatFarkas` evidence for the bad row-sum contradiction.
For exact tests, it recomputes binomial coefficients and fixed-margin
hypergeometric sums directly; the bad Fisher row emits checked `UnsatFarkas`
evidence for the exact-rational p-value contradiction, and the bad tail-count
row emits a checked `UnsatDiophantine` certificate for the inconsistent integer
equalities.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-probability-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-random-variables-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-conditional-expectation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-stochastic-kernels-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-hitting-times-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-concentration-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-martingales-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-integration-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-product-measure-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_product_measure_bad_marginal_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-markov-chain-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/descriptive-statistics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-covariance-matrix-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-naive-bayes-classifier-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-confusion-matrix-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/least-squares-regression-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/exact-statistical-tests-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-measure-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-d-separation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/random-matrix-finite-v0
python3 scripts/query-foundational-resources.py checks --pack finite-probability-v0 --text Bayes --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-probability-v0 --text Bayes --proof-status checked --require-any
```

For a fuller trace through atom-table replay, read
[End To End: Conditional Probability, Random Variables, Kernels, Concentration, Martingales, And Product Measures](finite-probability-end-to-end.md).
For the single-pack finite-probability table story, read
[End To End: Finite Probability Mass Tables](finite-probability-mass-tables-end-to-end.md).
For the diagnostic-test Bayes posterior and checked bad-posterior row, read
[End To End: Finite Bayes Update](finite-bayes-update-end-to-end.md).
For a focused finite conditional-expectation trace, read
[End To End: Finite Conditional Expectation](finite-conditional-expectation-end-to-end.md).
For exact simple-function integration over finite atom tables, read
[End To End: Finite Integration](finite-integration-end-to-end.md) and
[Lebesgue Integration Theorem Boundary](lebesgue-integration-theorem-boundary.md).
For exact finite product-measure and Fubini replay, read
[End To End: Finite Product Measure](finite-product-measure-end-to-end.md) and
[Fubini Tonelli Theorem Boundary](fubini-tonelli-theorem-boundary.md).
For exact finite statistics and regression replay, read
[End To End: Descriptive Statistics And Regression](descriptive-statistics-regression-end-to-end.md).
For exact finite covariance replay, read
[End To End: Finite Covariance Matrix](covariance-matrix-end-to-end.md).
For exact finite Naive Bayes classifier replay, read
[End To End: Finite Naive Bayes Classifier](naive-bayes-classifier-end-to-end.md).
For exact finite classifier-metric replay, read
[End To End: Finite Classifier Metrics](classifier-metrics-end-to-end.md).
For finite matrix-valued probability tables, read
[End To End: Finite Random Matrices](random-matrix-finite-end-to-end.md).
For the cross-pack finite random-matrix query map, read
[Random Matrix Moment Index](random-matrix-moment-index.md).
For exact finite statistical-test p-values, read
[End To End: Exact Statistical Tests](exact-statistical-tests-end-to-end.md).
For finite counting identities and the first pigeonhole refutation, read
[End To End: Counting And Pigeonhole](counting-pigeonhole-end-to-end.md).
For finite DAG d-separation path replay, read
[End To End: DAG D-Separation Checks](graph-d-separation-end-to-end.md) and
[D-Separation Causal Trust Boundary](d-separation-causal-trust-boundary.md).
For finite sigma-algebras and exact measure tables, read
[End To End: Finite Measure](finite-measure-end-to-end.md). For the
topology-to-measure bridge, read
[End To End: Finite Topology And Measure](finite-topology-measure-end-to-end.md).

## Proof Upgrade Notes

Finite probability tables, random variables, kernels, martingales, product
measures, Markov chains, d-separation rows, exact statistics, finite
covariance matrices, finite Naive Bayes classifiers, and random-matrix moments first use
[Finite Model Replay](../../proof-cookbook/recipes/finite-model-replay.md):
the validator recomputes exact atom-table sums and finite path conditions.
Malformed probability normalization, Bayes-posterior rows, measure-complement
rows, conditional expectation tables, stochastic rows, expected hitting-time
equations, tail bounds, regression coefficients, covariance entries, classifier
posteriors, and
random-matrix moment/rank rows graduate through
[QF_LRA / Farkas Evidence](../../proof-cookbook/recipes/qf-lra-farkas.md).
Discrete count contradictions such as contingency totals and exact tail counts
use
[QF_LIA / Diophantine Evidence](../../proof-cookbook/recipes/qf-lia-diophantine.md).
General measure-theory, stochastic-process, concentration, asymptotic
statistics, and causal-identification results remain under the
[Lean Horizon](../../proof-cookbook/recipes/lean-horizon-template.md) route or
need explicit numerical reproducibility metadata before they become resource
claims.

## Horizon

Continuous distributions, stochastic processes, convergence theorems, random
matrix spectral laws, Chernoff/Hoeffding bounds, laws of large numbers,
central limit theorems, martingale concentration, Lebesgue integration,
monotone and dominated convergence, general product measures, Fubini/Tonelli, conditional
expectation, regular conditional probabilities, disintegration theorems,
general Markov kernels, recurrence/transience classifications,
infinite-horizon hitting probabilities, general martingale convergence,
optional stopping, Doob inequalities, MCMC, HMC, variational inference,
asymptotic statistical tests, covariance-estimator consistency, PCA theorem
claims, calibration, causal identification, do-calculus, and floating-point
diagnostics are not proof claims. They need either
Lean-backed probability/measure formalization or explicit reproducibility
metadata with seeds and tolerances.
