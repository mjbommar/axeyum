# End To End: Finite Precision Recall

Precision-recall evaluation starts with a scored result table:

```text
class label + score -> score ranking -> precision-recall points -> average precision
```

This resource checks one finite exact-rational version of that pattern. It is
not a statistical guarantee and it does not prove that any threshold is optimal.

## Source Data

The pack
[`finite-precision-recall-v0`](../../../artifacts/examples/math/finite-precision-recall-v0/README.md)
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
FN = 1
precision = 2/3
recall = 2/3
F1 = 2/3
```

## Precision-Recall Curve And AP

Scanning the sorted rows gives:

| After | TP | FP | Recall | Precision |
|---|---:|---:|---:|---:|
| `start` | `0` | `0` | `0` | `1` |
| `p_high` | `1` | `0` | `1/3` | `1` |
| `n_high` | `1` | `1` | `1/3` | `1/2` |
| `p_mid` | `2` | `1` | `2/3` | `2/3` |
| `n_mid` | `2` | `2` | `2/3` | `1/2` |
| `p_low` | `3` | `2` | `1` | `3/5` |
| `n_low` | `3` | `3` | `1` | `1/2` |

Average precision averages precision at positive hits:

```text
positive-hit precisions = 1, 2/3, 3/5
sum = 34/15
average precision = 34/45
```

## What Axeyum Checks

The validator checks four replay rows:

- score order and class counts;
- threshold precision/recall/F1;
- the precision-recall curve;
- average precision.

Then it checks a malformed claim:

```text
claimed average precision = 3/4
```

Exact replay rejects that because the committed table gives `34/45`. The
separate checked proof row isolates the arithmetic contradiction:

```text
45 * ap = 34
4 * ap = 3
```

The QF_LRA/Farkas regression parses the source SMT-LIB artifact, emits
`UnsatFarkas` evidence, and checks the certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed score table;
- exact rational replay of threshold, precision-recall, and average-precision
  definitions;
- independent checking of the Farkas certificate for the malformed scalar row.

Untrusted or out of scope:

- threshold selection or optimality;
- calibration, risk bounds, or confidence intervals;
- general precision-recall theorems;
- tie-policy or interpolation-policy coverage beyond this tie-free finite
  table;
- continuous score-distribution theory;
- floating-point classifier or metric implementation behavior.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-precision-recall-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_precision_recall_bad_average_precision_artifact_emits_checked_farkas
```

Useful queries:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-precision-recall-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_precision_recall_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "precision recall" \
  --require-any
```
