# End To End: Finite Calibration And Brier Score

Probabilistic classifier evaluation starts with forecast probabilities:

```text
actual label + predicted probability -> calibration bins -> Brier score
```

This resource checks one finite exact-rational version of that pattern. It is
not a statistical guarantee, it does not prove that the binning policy is
canonical, and it does not prove model calibration.

## Source Data

The pack
[`finite-calibration-brier-v0`](../../../artifacts/examples/math/finite-calibration-brier-v0/README.md)
uses six probability forecasts:

| Row | Actual Class | Positive Probability |
|---|---|---:|
| `low_a` | `negative` | `1/10` |
| `low_b` | `negative` | `1/5` |
| `mid_pos` | `positive` | `2/5` |
| `high_pos` | `positive` | `3/5` |
| `top_pos` | `positive` | `4/5` |
| `top_neg` | `negative` | `9/10` |

There are three positive rows and three negative rows.

## Calibration Bins

The pack fixes two bins:

```text
low bin  = positive_probability < 1/2
high bin = positive_probability >= 1/2
```

Exact replay computes:

| Bin | Rows | Average Prediction | Observed Positive Rate | Absolute Gap | Weighted Gap |
|---|---|---:|---:|---:|---:|
| `low` | `low_a`, `low_b`, `mid_pos` | `7/30` | `1/3` | `1/10` | `1/20` |
| `high` | `high_pos`, `top_pos`, `top_neg` | `23/30` | `2/3` | `1/10` | `1/20` |

The fixed two-bin expected calibration error is:

```text
ECE = 1/20 + 1/20 = 1/10
```

## Brier Score

Encode positive labels as `1` and negative labels as `0`. The Brier score is
the mean squared forecast error:

| Row | Residual `p - y` | Squared Error |
|---|---:|---:|
| `low_a` | `1/10` | `1/100` |
| `low_b` | `1/5` | `1/25` |
| `mid_pos` | `-3/5` | `9/25` |
| `high_pos` | `-2/5` | `4/25` |
| `top_pos` | `-1/5` | `1/25` |
| `top_neg` | `9/10` | `81/100` |

The squared errors sum to `71/50`, so:

```text
Brier score = (71/50) / 6 = 71/300
```

## What Axeyum Checks

The validator checks four replay rows:

- probability table and class counts;
- fixed calibration-bin summaries;
- expected calibration error;
- Brier score.

Then it checks a malformed claim:

```text
claimed Brier score = 1/5
```

Exact replay rejects that because the committed table gives `71/300`. The
separate checked proof row isolates the arithmetic contradiction:

```text
300 * brier = 71
5 * brier = 1
```

The QF_LRA/Farkas regression parses the source SMT-LIB artifact, emits
`UnsatFarkas` evidence, and checks the certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed forecast table;
- exact rational replay of the fixed calibration-bin and Brier-score
  definitions;
- independent checking of the Farkas certificate for the malformed scalar row.

Untrusted or out of scope:

- calibration of any model family;
- binning-policy optimality or canonical bin choice;
- proper-scoring-rule theorems;
- risk bounds, sampling guarantees, or confidence intervals;
- continuous score-distribution theory;
- floating-point classifier or metric implementation behavior.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-calibration-brier-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_calibration_brier_bad_brier_score_artifact_emits_checked_farkas
```

Useful queries:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-calibration-brier-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_calibration_brier_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text calibration \
  --require-any
```
