# Model

All numeric data is exact rational data interpreted as real-number data. This
keeps the replay checker deterministic while still teaching the algebraic
fragment of real reasoning.

The ordered-field midpoint row checks:

```text
1 < 3/2 < 2
3/2 = (1 + 2) / 2
```

The nonlinear product row checks:

```text
x = 3/2
y = 4/3
x >= 1
y >= 1
x * y = 2
x * y >= 1
```

The quadratic root row uses coefficients in ascending order:

```text
p(x) = 9/4 - 3*x + x^2
p(3/2) = 0
```

The first UNSAT row is the fixed square nonnegativity shape:

```text
exists x. x^2 < 0
```

The second UNSAT row is a one-variable quadratic with negative discriminant:

```text
exists x. x^2 + 1 = 0
discriminant = -4
```

The final row records that completeness and general epsilon-delta reasoning are
not consequences of these finite algebraic checks.
