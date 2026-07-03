# Model

The model fixes two identical positive rational intervals and computes their
sum and product exactly.

## Symbols

| Symbol | Meaning | Value |
|---|---|---|
| `X` | first closed interval | `[1, 10001/10000]` |
| `Y` | second closed interval | `[1, 10001/10000]` |
| `X + Y` | interval sum | `[2, 10001/5000]` |
| `X * Y` | interval product | `[1, 100020001/100000000]` |
| `width(X)` | upper minus lower | `1/10000` |
| `width(Y)` | upper minus lower | `1/10000` |
| `width(X + Y)` | sum width | `1/5000` |
| `width(X * Y)` | product width | `20001/100000000` |
| `linearized_product_upper` | upper bound that drops the second-order term | `5001/5000` |
| `second_order_term` | `width(X) * width(Y)` | `1/100000000` |

## Encoding Sketch

Because both input intervals are nonnegative, the product enclosure is just the
endpoint product:

```text
lower(X * Y) = lower(X) * lower(Y)
upper(X * Y) = upper(X) * upper(Y)
```

The checked QF_LRA artifact isolates only the final scalar contradiction:

```text
product_upper = 100020001/100000000
product_upper <= 5001/5000
```

The richer interval arithmetic is replayed by the resource validator before
that scalar conflict is trusted.
