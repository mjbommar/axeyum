# End To End: Finite Naive Bayes Classifier

Naive Bayes is a classifier pattern:

```text
class prior * feature likelihoods -> class score -> normalized posterior
```

This resource checks one finite exact-rational version of that pattern. It is
not a statistical guarantee and it does not prove that the independence model
is true.

## Source Data

The pack
[`finite-naive-bayes-classifier-v0`](../../../artifacts/examples/math/finite-naive-bayes-classifier-v0/README.md)
uses six training rows:

| Row | Class | Symptom | Lab Positive |
|---|---|---|---|
| `p0` | `positive` | `present` | `present` |
| `p1` | `positive` | `present` | `absent` |
| `p2` | `positive` | `absent` | `present` |
| `n0` | `negative` | `present` | `absent` |
| `n1` | `negative` | `absent` | `present` |
| `n2` | `negative` | `absent` | `absent` |

There are three examples in each class. With Laplace smoothing `alpha = 1`
over two feature values:

```text
P(symptom=present | positive) = 3/5
P(lab_positive=present | positive) = 3/5
P(symptom=present | negative) = 2/5
P(lab_positive=present | negative) = 2/5
```

For the observed feature vector `(present, present)`, exact replay computes:

```text
score_positive = (1/2) * (3/5) * (3/5) = 9/50
score_negative = (1/2) * (2/5) * (2/5) = 2/25
evidence_score = 13/50
P(positive | features) = 9/13
P(negative | features) = 4/13
```

The finite decision is `positive`.

## What Axeyum Checks

The validator checks four replay rows:

- training row counts and binary feature counts;
- smoothed likelihoods;
- unnormalized class scores;
- normalized posterior probabilities and the decision margin.

Then it checks a malformed claim:

```text
claimed P(positive | features) = 2/3
```

Exact replay rejects that because the committed table gives `9/13`. The
separate checked proof row isolates the arithmetic contradiction:

```text
13 * p_positive = 9
3 * p_positive = 2
```

The QF_LRA/Farkas regression parses the source SMT-LIB artifact, emits
`UnsatFarkas` evidence, and checks the certificate independently.

## Trust Boundary

Trusted:

- exact rational replay of the committed training table;
- exact replay of the smoothing formula and posterior normalization;
- independent checking of the Farkas certificate for the malformed scalar row.

Untrusted or out of scope:

- whether conditional independence is a good model for a real dataset;
- Bayes optimality or calibration;
- sampling guarantees, consistency, and asymptotics;
- floating-point classifier implementation behavior.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-naive-bayes-classifier-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_naive_bayes_classifier_bad_posterior_artifact_emits_checked_farkas
```

Useful queries:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-naive-bayes-classifier-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_naive_bayes_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "naive bayes" \
  --require-any
```
