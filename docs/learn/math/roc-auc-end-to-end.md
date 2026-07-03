# End To End: Finite ROC AUC

ROC/AUC starts with a scored result table:

```text
class label + score -> score ranking -> ROC points -> area under the curve
```

This resource checks one finite exact-rational version of that pattern. It is
not a statistical guarantee and it does not prove that any threshold is optimal.

## Source Data

The pack
[`finite-roc-auc-v0`](../../../artifacts/examples/math/finite-roc-auc-v0/README.md)
uses six scored rows:

| Row | Class | Score |
|---|---|---:|
| `p_high` | `positive` | `9/10` |
| `n_high` | `negative` | `4/5` |
| `p_mid` | `positive` | `7/10` |
| `n_mid` | `negative` | `3/5` |
| `p_low` | `positive` | `2/5` |
| `n_low` | `negative` | `1/5` |

Exact replay sorts the rows as:

```text
p_high, n_high, p_mid, n_mid, p_low, n_low
```

There are three positive rows and three negative rows.

## Threshold Point

At threshold `score >= 7/10`, the predicted-positive rows are `p_high`,
`n_high`, and `p_mid`, so exact replay computes:

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

## ROC And AUC

Scanning the sorted rows gives:

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

The trapezoid area under the finite ROC staircase is also `2/3`.

## What Axeyum Checks

The validator checks four replay rows:

- score order and class counts;
- threshold operating-point counts and rates;
- the ROC staircase;
- pairwise AUC and trapezoid area.

Then it checks a malformed claim:

```text
claimed AUC = 3/4
```

Exact replay rejects that because the committed table gives `2/3`. The separate
checked proof row isolates the arithmetic contradiction:

```text
3 * auc = 2
4 * auc = 3
```

The QF_LRA/Farkas regression parses the source SMT-LIB artifact, emits
`UnsatFarkas` evidence, and checks the certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed score table;
- exact rational replay of threshold, ROC, and AUC definitions;
- independent checking of the Farkas certificate for the malformed scalar row.

Untrusted or out of scope:

- threshold selection or optimality;
- calibration, risk bounds, or confidence intervals;
- general ROC/AUC theorems;
- tie-policy coverage beyond this tie-free finite table;
- continuous score-distribution theory;
- floating-point classifier or metric implementation behavior.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-roc-auc-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_roc_auc_bad_auc_artifact_emits_checked_farkas
```

Useful queries:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-roc-auc-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_roc_auc_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "roc auc" \
  --require-any
```
