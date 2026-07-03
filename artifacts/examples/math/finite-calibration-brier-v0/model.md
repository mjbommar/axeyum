# Model

The finite forecast table has two classes and one exact rational predicted
probability for the positive class per row.

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

The pack uses two fixed bins:

```text
low bin  = p < 1/2
high bin = p >= 1/2
```

The low bin contains `low_a`, `low_b`, and `mid_pos`:

```text
average prediction = (1/10 + 1/5 + 2/5) / 3 = 7/30
observed positive rate = 1/3
absolute gap = 1/10
weighted gap = (3/6) * (1/10) = 1/20
```

The high bin contains `high_pos`, `top_pos`, and `top_neg`:

```text
average prediction = (3/5 + 4/5 + 9/10) / 3 = 23/30
observed positive rate = 2/3
absolute gap = 1/10
weighted gap = (3/6) * (1/10) = 1/20
```

The expected calibration error for this fixed two-bin summary is:

```text
ECE = 1/20 + 1/20 = 1/10
```

## Brier Score

Encode the actual class as `1` for positive and `0` for negative. The squared
forecast errors are:

| Row | Residual `p - y` | Squared Error |
|---|---:|---:|
| `low_a` | `1/10` | `1/100` |
| `low_b` | `1/5` | `1/25` |
| `mid_pos` | `-3/5` | `9/25` |
| `high_pos` | `-2/5` | `4/25` |
| `top_pos` | `-1/5` | `1/25` |
| `top_neg` | `9/10` | `81/100` |

The sum of squared errors is:

```text
1/100 + 1/25 + 9/25 + 4/25 + 1/25 + 81/100 = 71/50
```

The mean Brier score is:

```text
(71/50) / 6 = 71/300
```

The checked source artifact isolates the malformed claim `brier = 1/5` as:

```text
300 * brier = 71
5 * brier = 1
```
