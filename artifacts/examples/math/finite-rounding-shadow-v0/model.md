# Model

The model fixes one rational addition and one explicit three-decimal rounding
grid.

## Symbols

| Symbol | Meaning | Value |
|---|---|---|
| `x` | base rational value | `1` |
| `y` | small rational increment | `1/10000` |
| `exact_sum` | exact rational sum `x + y` | `10001/10000` |
| `exact_delta` | exact rational increment `exact_sum - x` | `1/10000` |
| `decimal_places` | fixed decimal precision | `3` |
| `scale` | grid scale `10^decimal_places` | `1000` |
| `rounded_x` | nearest-grid value for `x` | `1` |
| `rounded_y` | nearest-grid value for `y` | `0` |
| `rounded_sum` | nearest-grid value for `exact_sum` | `1` |
| `rounded_delta_after_sum` | `rounded_sum - rounded_x` | `0` |

## Encoding Sketch

The validator treats rounding as a checked rational transcript:

```text
scaled_value = scale * value
rounded_value = rounded_units / scale
residual = scaled_value - rounded_units
-1/2 <= residual < 1/2
```

For this instance, `scale * exact_sum = 10001/10`, so rounded units `1000`
have residual `1/10`, which is inside the nearest-grid cell.

The checked QF_LRA artifact isolates only the scalar contradiction:

```text
exact_delta = 1/10000
rounded_delta_after_sum = 0
exact_delta = rounded_delta_after_sum
```

That conflict is linear arithmetic over exact rationals.
