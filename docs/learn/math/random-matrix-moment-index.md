# Random Matrix Moment Index

This index keeps random-matrix resources finite and exact. It connects
matrix-valued atom tables, exact rational moments, expected Gram matrices,
rank-mixture probabilities, and checked bad moment/rank refutations without turning
finite enumeration into asymptotic random matrix theory.

The trust pattern is:

```text
untrusted fast search -> atom table, moment claim, Gram claim, rank claim, or bad-row candidate
trusted small checking -> exact probability normalization and finite matrix replay
proof upgrade -> checked QF_LRA/Farkas evidence for false finite moment/rank claims
remaining horizon -> asymptotic spectra, universality, concentration theorems, and simulations
```

## Concept Rows

- `bridge_random_matrix_finite_moment`
- `bridge_pushforward_distribution`
- `bridge_finite_probability_mass_table`
- `bridge_finite_tail_count_obstruction`
- `bridge_rank_nullity`
- `bridge_eigenpair`
- `bridge_characteristic_polynomial`
- `bridge_qf_lra_farkas_anatomy`
- `field_probability_theory`
- `field_statistics`
- `field_linear_algebra`
- `field_numerical_analysis`
- `curriculum_counting`
- `curriculum_rationals`
- `curriculum_linear_algebra`

These rows live in the
[Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json).

## Resource Map

| Question | Packs | Trusted Check | Horizon |
|---|---|---|---|
| Is a matrix-valued distribution normalized? | `random-matrix-finite-v0`, `finite-probability-v0` | exact rational atom-sum replay | continuous distributions and measure-theoretic probability |
| What are the listed matrix moments? | `random-matrix-finite-v0` | finite enumeration of trace, trace-square, determinant, and weighted expectations | asymptotic spectral laws |
| What is the expected Gram or covariance matrix? | `random-matrix-finite-v0`, `finite-covariance-matrix-v0` | exact `A^T*A` replay for every atom, centered-row Gram replay, and covariance entry replay | covariance/operator limit theorems |
| What is the rank distribution? | `random-matrix-finite-v0` | exact finite rank computation by rational row reduction, expectation replay, and checked rejection of a bad expected rank | rank laws for matrix ensembles |
| Is a moment or rank claim false? | `random-matrix-finite-v0` | exact replay computes the value, then checked QF_LRA/Farkas rejects the conflicting value | concentration or universality theorems |
| Which adjacent packs reuse the same finite-table pattern? | `descriptive-statistics-v0`, `finite-covariance-matrix-v0`, `finite-concentration-v0`, `finite-random-variables-v0` | exact finite statistic, covariance, tail, or pushforward replay | asymptotic inference and stochastic-process limits |

## Checkable Shapes

The diagonal-sign distribution is finite data:

```text
pp = [[ 1, 0], [0,  1]]
pn = [[ 1, 0], [0, -1]]
np = [[-1, 0], [0,  1]]
nn = [[-1, 0], [0, -1]]
probability of each atom = 1/4
```

The checker recomputes normalization, then each atom's trace and determinant:

```text
trace:        2,  0,  0, -2
trace^2:      4,  0,  0,  4
determinant:  1, -1, -1,  1
```

The trusted finite expectations are:

```text
E[trace(A)] = 0
E[trace(A)^2] = 2
E[det(A)] = 0
P(A is invertible) = 1
```

The expected Gram row is also finite:

```text
A^T * A = I
E[A^T * A] = I
```

The rank-mixture row is finite row reduction:

```text
rank([[0, 0], [0, 0]]) = 0
rank([[1, 1], [1, 1]]) = 1
rank([[1, 0], [0, 1]]) = 2
P(rank = 0) = P(rank = 1) = P(rank = 2) = 1/3
E[rank(A)] = 1
```

The bad expected-rank row claims:

```text
E[rank(A)] = 2
```

After replay computes `E[rank(A)] = 1`, the proof route checks:

```text
expected_rank = 1
expected_rank = 2
```

The bad row claims:

```text
E[trace(A)^2] = 1
```

After replay computes `E[trace(A)^2] = 2`, the proof route checks the tiny
rational contradiction:

```text
expected_trace_square = 2
expected_trace_square = 1
```

That is enough for checked QF_LRA/Farkas evidence. It is not evidence for a
random-matrix limit law.

## Use The Lessons

Start with [Finite Random Matrices](random-matrix-finite-end-to-end.md) for the
single-pack trace through atom tables, moments, expected Gram matrices, rank
probabilities, bad expected-rank rejection, and bad trace-square rejection.
Use [Finite Covariance Matrix](covariance-matrix-end-to-end.md) for the
finite-sample mean, centered Gram, covariance, positive-semidefinite shadow,
and bad covariance-entry row.

Use [Probability And Statistics](probability-and-statistics.md) for the
surrounding finite-probability cluster: finite mass tables, random variables,
conditional expectation, stochastic kernels, hitting times, concentration,
martingales, product measures, exact tests, and finite statistics.

Use [Matrix Computation Index](matrix-computation-index.md) when the same row
needs to be viewed as a matrix-computation artifact alongside residuals,
eigenpairs, characteristic polynomials, operators, tensors, and chain/cochain
matrices.

## Query It

From the repository root:

```sh
python3 scripts/query-foundational-resources.py concepts --field probability_theory --text random --require-any
python3 scripts/query-foundational-resources.py packs --concept bridge_random_matrix_finite_moment --route Farkas --require-any
python3 scripts/query-foundational-resources.py checks --concept bridge_random_matrix_finite_moment --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack random-matrix-finite-v0 --route Farkas --proof-status checked --text rank --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-covariance-matrix-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --field probability_theory --route Farkas --proof-status checked --require-any
```

## Replay It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/random-matrix-finite-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-covariance-matrix-v0
```

Expected shape:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

The checked rows prove only the listed finite rational rows: atom
normalization, trace and determinant moments, expected Gram matrices,
rank-mixture probabilities, and the bad expected-rank and trace-square
contradictions. They do
not prove semicircle laws, Marchenko-Pastur laws, universality, concentration
theorems for matrix ensembles, high-dimensional limits, floating-point
simulation correctness, or numerical eigensolver behavior. Those remain
Lean-horizon or numerical-honesty work until there are kernel-checked or
explicitly reproducible artifacts.
