# Model

The finite classifier table has two classes and one exact rational score per
row.

| Row | Class | Score |
|---|---|---|
| `p_high` | `positive` | `9/10` |
| `n_high` | `negative` | `4/5` |
| `p_mid` | `positive` | `7/10` |
| `n_mid` | `negative` | `3/5` |
| `p_low` | `positive` | `2/5` |
| `n_low` | `negative` | `1/5` |

The descending score order is:

```text
p_high, n_high, p_mid, n_mid, p_low, n_low
```

The class counts are:

```text
positives = 3
negatives = 3
total = 6
```

At threshold `score >= 7/10`, the predicted-positive rows are `p_high`,
`n_high`, and `p_mid`, so:

```text
TP = 2
FP = 1
TN = 2
FN = 1
TPR = recall = sensitivity = 2/3
FPR = 1/3
precision = 2/3
specificity = 2/3
```

The ROC staircase from scanning the sorted rows is:

| After | FPR | TPR |
|---|---:|---:|
| `start` | `0` | `0` |
| `p_high` | `0` | `1/3` |
| `n_high` | `1/3` | `1/3` |
| `p_mid` | `1/3` | `2/3` |
| `n_mid` | `2/3` | `2/3` |
| `p_low` | `2/3` | `1` |
| `n_low` | `1` | `1` |

Pairwise AUC compares every positive row with every negative row:

```text
positive-negative pairs = 9
positive wins = 6
ties = 0
AUC = 6/9 = 2/3
```

The trapezoid area under the ROC staircase also equals `2/3`.

The checked malformed row isolates the final scalar AUC equation:

```text
3 * auc = 2
4 * auc = 3
```

The first equation comes from exact replay. The second is the false claim
`auc = 3/4`.
