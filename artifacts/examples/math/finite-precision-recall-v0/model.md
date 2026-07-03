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
FN = 1
predicted positives = 3
precision = 2/3
recall = 2/3
F1 = 2/3
```

The precision-recall curve from scanning the sorted rows is:

| After | TP | FP | Recall | Precision |
|---|---:|---:|---:|---:|
| `start` | `0` | `0` | `0` | `1` |
| `p_high` | `1` | `0` | `1/3` | `1` |
| `n_high` | `1` | `1` | `1/3` | `1/2` |
| `p_mid` | `2` | `1` | `2/3` | `2/3` |
| `n_mid` | `2` | `2` | `2/3` | `1/2` |
| `p_low` | `3` | `2` | `1` | `3/5` |
| `n_low` | `3` | `3` | `1` | `1/2` |

This pack uses the standard finite ranking average-precision replay: average
the precision values at positive hits.

```text
positive-hit precisions = 1, 2/3, 3/5
sum = 34/15
average precision = (34/15) / 3 = 34/45
```

The checked malformed row isolates the final scalar average-precision
equation:

```text
45 * ap = 34
4 * ap = 3
```

The first equation comes from exact replay. The second is the false claim
`ap = 3/4`.
