# Model

The checked finite model is the ODE

```text
y' = -y
y(0) = 1
h = 1/2
```

The starter is the backward-Euler value:

```text
y_1 = y_0 + h * (-y_1)
y_1 = 1 + (1/2) * (-y_1)
y_1 = 2/3
```

BDF2 is encoded as:

```text
(3*y_(n+1) - 4*y_n + y_(n-1)) / (2h) = f(t_(n+1), y_(n+1))
```

Because `2h = 1`, the replayed obligations are:

```text
3*y_(n+1) - 4*y_n + y_(n-1) = -y_(n+1)
```

The listed trace is:

```text
times  = 0, 1/2, 1, 3/2
states = 1, 2/3, 5/12, 1/4
```

First BDF2 update:

```text
3*(5/12) - 4*(2/3) + 1 = -5/12
f(1, 5/12) = -5/12
```

Second BDF2 update:

```text
3*(1/4) - 4*(5/12) + 2/3 = -1/4
f(3/2, 1/4) = -1/4
```

The finite monotone row checks only that this listed trace is positive,
bounded by `1`, and strictly decreasing.
