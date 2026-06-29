# Model

Explicit Euler is checked as a finite rational transition system:

```text
y_{n+1} = y_n + h * f(t_n, y_n)
t_{n+1} = t_n + h
```

All rows use exact rational strings for time, state, derivative, and error
values.

## Linear Decay

For `y' = -y`, step `h = 1/2`, and initial value `y(0) = 1`, the trace is:

```text
1, 1/2, 1/4, 1/8
```

Each step multiplies the previous state by `1/2`.

## Polynomial Forcing

For `y' = 2t`, `y(0) = 0`, and the same step size, the Euler trace is:

```text
0, 0, 1/2, 3/2
```

The exact polynomial solution is `y = t^2`, so on the grid
`0, 1/2, 1, 3/2`, the exact values are:

```text
0, 1/4, 1, 9/4
```

The listed absolute errors are checked exactly.

## Invariant And Bad Step

The linear-decay trace remains inside `[0, 1]` and is monotone nonincreasing.
The bad-step row rejects the claim that a single Euler step from `y = 1` gives
`3/4`; the exact next state is `1/2`.

These rows are finite replay targets, not a full ODE or numerical-analysis
library.
