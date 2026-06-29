# Model

Variables, coefficients, bounds, witness values, and multipliers are exact
rationals written as strings accepted by Python's `Fraction` type.

Linear inequalities are represented in canonical `<=` form:

```json
{
  "coefficients": {"x": "1", "y": "2"},
  "bound": "5"
}
```

which means:

```text
x + 2y <= 5
```

## Checks

### Feasible Point

The base feasible region is:

```text
x >= 0
y >= 0
x + y <= 4
x + 2y <= 5
```

The witness `x = 1`, `y = 2` satisfies every inequality.

### Objective Threshold Witness

The same feasible region admits the threshold `x + y >= 4` using the witness
`x = 3`, `y = 1`.

### Farkas Infeasible Threshold

The threshold `x + y >= 5` is incompatible with the base constraint
`x + y <= 4`.

The pack writes the threshold as `-x - y <= -5`. The Farkas certificate uses
multiplier `1` for `x + y <= 4` and multiplier `1` for `-x - y <= -5`, giving:

```text
0*x + 0*y <= -1
```

which is impossible. This is a tiny checked certificate, not a general LP
duality theorem. The Axeyum regression also checks the same fixed conflict as
a conjunctive `QF_LRA` query:

```text
x + y <= 4
x + y >= 5
```

That query emits `UnsatFarkas` evidence, and the certificate arithmetic is
rechecked independently.
