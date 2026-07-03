# Model

The finite model is a deterministic exact-rational implicit transition system.

Fixed ODE:

```text
f(t, y) = -y
y(0) = 1
h = 1/2
```

Backward Euler is encoded as:

```text
endpoint_time = t_n + h
endpoint_derivative = f(endpoint_time, y_(n+1))
y_(n+1) = y_n + h*endpoint_derivative
```

For this ODE:

```text
y_(n+1) = y_n - (1/2)*y_(n+1)
(3/2)*y_(n+1) = y_n
y_(n+1) = (2/3)*y_n
```

The witness trace is:

```text
times  = 0, 1/2, 1, 3/2
states = 1, 2/3, 4/9, 8/27
```

The endpoint table is:

```text
n=0: endpoint=1/2, derivative=-2/3, residual=1 + (1/2)*(-2/3) - 2/3 = 0
n=1: endpoint=1,   derivative=-4/9, residual=2/3 + (1/2)*(-4/9) - 4/9 = 0
n=2: endpoint=3/2, derivative=-8/27, residual=4/9 + (1/2)*(-8/27) - 8/27 = 0
```

The finite decay table is:

```text
state       1    2/3   4/9   8/27
ratio            2/3   2/3   2/3
bounds      0 <= state <= 1
```

The checked negative row isolates only the first-step scalar contradiction:

```text
backward_euler_next_state = 2/3
backward_euler_next_state = 1/2
```

That is intentionally small. The pack is a finite exact replay resource, not a
proof of the general backward Euler method.
