# End To End: Finite Probability Mass Tables

This lesson follows one exact finite probability resource from atom-table
normalization to conditional probability, Bayes replay, finite independence,
and checked rejection of malformed exact-rational probability claims. It uses the
[finite-probability-v0](../../../artifacts/examples/math/finite-probability-v0/)
pack.

Concept rows:

- `field_probability_theory`, `field_statistics`, and `field_measure_theory`
  in the [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_counting`, `curriculum_rationals`, and `curriculum_sets` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `bridge_probability_mass_table` and `family_exact_rational_farkas` in the
  atlas bridge/example-family vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `pmf-total-mass` | `sat` | replay-only |
| `bad-normalization-rejected` | `unsat` | checked QF_LRA/Farkas |
| `conditional-probability-witness` | `sat` | replay-only |
| `bad-conditional-probability-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bayes-posterior-witness` | `sat` | replay-only |
| `bad-bayes-posterior-rejected` | `unsat` | checked QF_LRA/Farkas |
| `independence-witness` | `sat` | replay-only |
| `bad-independence-rejected` | `unsat` | checked QF_LRA/Farkas |

Every row is finite and exact-rational. The pack checks probability mass
tables, conditional probabilities, Bayes posterior equations, and finite
independence equations. It does not cover continuous distributions, sampling
guarantees, asymptotic statistics, or measure-theoretic probability theorems.

## Encode A PMF

The normalized probability mass function is a fair die:

```text
P(one) = 1/6
P(two) = 1/6
P(three) = 1/6
P(four) = 1/6
P(five) = 1/6
P(six) = 1/6
```

The trusted replay checks each atom mass is in `[0,1]` and the total is:

```text
1/6 + 1/6 + 1/6 + 1/6 + 1/6 + 1/6 = 1
```

## Reject Bad Normalization

The bad normalization row uses a two-atom fair coin:

```text
P(heads) = 1/2
P(tails) = 1/2
```

Replay computes:

```text
P(heads) + P(tails) = 1
```

The malformed claim also asserts:

```text
total = 3/2
```

The committed SMT-LIB artifact
[`bad-normalization-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-probability-v0/smt2/bad-normalization-farkas-conflict.smt2)
checks this final exact-linear contradiction through rechecked
`UnsatFarkas` evidence.

## Replay Conditional Probability

The conditional-probability witness is a four-atom joint table:

```text
P(rain_late) = 1/10
P(rain_on_time) = 1/5
P(dry_late) = 1/5
P(dry_on_time) = 1/2
```

The checker recomputes:

```text
P(rain) = 1/10 + 1/5 = 3/10
P(late and rain) = 1/10
P(late | rain) = (1/10) / (3/10) = 1/3
```

No solver trust is needed for this row; it is exact finite replay.

## Reject Bad Conditional Probability

The bad conditional row keeps the same atom table but claims:

```text
P(late | rain) = 1/2
```

Replay still computes `P(rain) = 3/10` and `P(late and rain) = 1/10`. The
committed SMT-LIB artifact
[`bad-conditional-probability-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-probability-v0/smt2/bad-conditional-probability-farkas-conflict.smt2)
checks the division-free exact-linear contradiction:

```text
P(rain) * p = P(late and rain)
p = 1/2
```

with rechecked `UnsatFarkas` evidence.

## Replay Bayes

The diagnostic-test witness is:

```text
P(disease) = 1/100
P(positive | disease) = 9/10
P(positive | not disease) = 1/20
```

Replay computes:

```text
P(disease and positive) = 9/1000
P(positive) = 117/2000
P(disease | positive) = (9/1000) / (117/2000) = 2/13
```

The bad Bayes row keeps the same source parameters but claims posterior `1/5`.
The committed artifact
[`bad-bayes-posterior-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-probability-v0/smt2/bad-bayes-posterior-farkas-conflict.smt2)
checks the exact equation:

```text
P(positive) * posterior = P(disease and positive)
posterior = 1/5
```

against the replayed source values. The Farkas checker, not solver search, is
the trusted evidence.

## Replay Finite Independence

The independence witness is a four-atom product table:

```text
P(heads and red) = 1/4
P(heads and blue) = 1/4
P(tails and red) = 1/4
P(tails and blue) = 1/4
```

Replay computes:

```text
P(heads) = 1/2
P(red) = 1/2
P(heads and red) = 1/4
```

The bad independence row keeps the marginal probabilities but claims
`P(heads and red)=1/3`. The committed artifact
[`bad-independence-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-probability-v0/smt2/bad-independence-farkas-conflict.smt2)
checks the exact-linear contradiction:

```text
joint_probability = independence_product
independence_product = 1/4
joint_probability = 1/3
```

The finite table replay computes the marginals; the trusted route checks only
the final Farkas certificate.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-probability-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_probability_bad_normalization_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_probability_bad_conditional_probability_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_probability_bad_bayes_posterior_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_probability_bad_independence_artifact_emits_checked_farkas
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> probability table, posterior, independence, or Farkas certificate
trusted small checking -> exact finite sums, rational division, checked QF_LRA evidence
remaining horizon -> continuous probability, sampling guarantees, asymptotics, and measure-theoretic theorems
```

For the broader finite-probability process path through random variables,
kernels, concentration, martingales, product measures, and finite integration,
read
[End To End: Conditional Probability, Random Variables, Kernels, Concentration, Martingales, And Product Measures](finite-probability-end-to-end.md).
