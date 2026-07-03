# Model

The finite classifier table has two actual classes and two predicted classes.

| Row | Actual | Predicted |
|---|---|---|
| `e0` | `positive` | `positive` |
| `e1` | `positive` | `positive` |
| `e2` | `positive` | `negative` |
| `e3` | `positive` | `negative` |
| `e4` | `negative` | `negative` |
| `e5` | `negative` | `negative` |
| `e6` | `negative` | `negative` |
| `e7` | `negative` | `positive` |

The confusion counts are:

```text
TP = 2
FP = 1
TN = 3
FN = 2
actual positives = 4
actual negatives = 4
predicted positives = 3
predicted negatives = 5
total = 8
```

The exact metrics are:

```text
accuracy = (TP + TN) / total = 5/8
precision = TP / (TP + FP) = 2/3
recall = TP / (TP + FN) = 1/2
specificity = TN / (TN + FP) = 3/4
negative predictive value = TN / (TN + FN) = 3/5
false positive rate = FP / (FP + TN) = 1/4
false negative rate = FN / (FN + TP) = 1/2
balanced accuracy = (recall + specificity) / 2 = 5/8
F1 = 2*TP / (2*TP + FP + FN) = 4/7
Jaccard = TP / (TP + FP + FN) = 2/5
```

The checked malformed row isolates the final scalar precision equation:

```text
3 * precision = 2
4 * precision = 3
```

The first equation comes from exact replay. The second is the false claim
`precision = 3/4`.
