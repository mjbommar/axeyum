# Model

The finite training table has two classes and two binary features.

| Row | Class | Symptom | Lab Positive |
|---|---|---|---|
| `p0` | `positive` | `present` | `present` |
| `p1` | `positive` | `present` | `absent` |
| `p2` | `positive` | `absent` | `present` |
| `n0` | `negative` | `present` | `absent` |
| `n1` | `negative` | `absent` | `present` |
| `n2` | `negative` | `absent` | `absent` |

There are three rows per class, so the class priors are both `1/2`.

Laplace smoothing uses `alpha = 1` over two feature values. For the observation

```text
symptom = present
lab_positive = present
```

the smoothed likelihoods are:

```text
P(symptom=present | positive) = (2 + 1) / (3 + 2) = 3/5
P(lab_positive=present | positive) = (2 + 1) / (3 + 2) = 3/5
P(symptom=present | negative) = (1 + 1) / (3 + 2) = 2/5
P(lab_positive=present | negative) = (1 + 1) / (3 + 2) = 2/5
```

The unnormalized class scores are:

```text
score_positive = (1/2) * (3/5) * (3/5) = 9/50
score_negative = (1/2) * (2/5) * (2/5) = 2/25
evidence_score = 9/50 + 2/25 = 13/50
```

The normalized posterior is:

```text
P(positive | features) = (9/50) / (13/50) = 9/13
P(negative | features) = (2/25) / (13/50) = 4/13
```

The finite classifier therefore predicts `positive` with posterior margin
`5/13`.

The checked malformed row isolates the final scalar posterior equation:

```text
13 * p_positive = 9
3 * p_positive = 2
```

The first equation comes from exact replay. The second is the false claim
`p_positive = 2/3`.
