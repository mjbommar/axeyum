# End To End: Finite Classifier Metrics

Classifier metrics start with a result table:

```text
actual label + predicted label -> confusion counts -> rates and scores
```

This resource checks one finite exact-rational version of that pattern. It is
not a statistical guarantee and it does not prove that the classifier will
generalize to future data.

## Source Data

The pack
[`finite-confusion-matrix-v0`](../../../artifacts/examples/math/finite-confusion-matrix-v0/README.md)
uses eight result rows:

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

Exact replay computes:

```text
TP = 2
FP = 1
TN = 3
FN = 2
total = 8
```

From those counts:

```text
accuracy = 5/8
precision = 2/3
recall = 1/2
specificity = 3/4
negative predictive value = 3/5
false positive rate = 1/4
false negative rate = 1/2
balanced accuracy = 5/8
F1 = 4/7
Jaccard = 2/5
```

## What Axeyum Checks

The validator checks four replay rows:

- confusion counts and class totals;
- exact accuracy;
- exact precision/recall/specificity/NPV/FPR/FNR;
- exact F1, balanced accuracy, and Jaccard index.

Then it checks a malformed claim:

```text
claimed precision = 3/4
```

Exact replay rejects that because the committed table gives `2/3`. The
separate checked proof row isolates the arithmetic contradiction:

```text
3 * precision = 2
4 * precision = 3
```

The QF_LRA/Farkas regression parses the source SMT-LIB artifact, emits
`UnsatFarkas` evidence, and checks the certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed actual/predicted table;
- exact rational replay of the metric definitions;
- independent checking of the Farkas certificate for the malformed scalar row.

Untrusted or out of scope:

- whether the classifier generalizes to unseen data;
- calibration, risk bounds, or confidence intervals;
- threshold selection, ROC/AUC, precision-recall curves, and ranking quality;
- sampling assumptions and statistical consistency;
- floating-point classifier or metric implementation behavior.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-confusion-matrix-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_confusion_matrix_bad_precision_artifact_emits_checked_farkas
```

Useful queries:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-confusion-matrix-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_classifier_metrics_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "classifier metrics" \
  --require-any
```
