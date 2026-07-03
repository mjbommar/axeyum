# Model

The finite model is a deterministic exact-rational implicit trapezoid
transition system.

Fixed ODE:

```text
f(t, y) = -y
y(0) = 1
h = 1/2
```

Crank-Nicolson is encoded as:

```text
start_derivative = f(t_n, y_n)
endpoint_time = t_n + h
endpoint_derivative = f(endpoint_time, y_(n+1))
averaged_derivative = (start_derivative + endpoint_derivative) / 2
y_(n+1) = y_n + h*averaged_derivative
```

For this ODE:

```text
y_(n+1) = y_n + (1/2) * ((-y_n - y_(n+1)) / 2)
y_(n+1) = y_n - (1/4)*y_n - (1/4)*y_(n+1)
(5/4)*y_(n+1) = (3/4)*y_n
y_(n+1) = (3/5)*y_n
```

The witness trace is:

```text
times  = 0, 1/2, 1, 3/2
states = 1, 3/5, 9/25, 27/125
```

The endpoint table is:

```text
n=0: start=-1,    endpoint=-3/5,   avg=-4/5,   residual=1 + (1/2)*(-4/5) - 3/5 = 0
n=1: start=-3/5, endpoint=-9/25,  avg=-12/25, residual=3/5 + (1/2)*(-12/25) - 9/25 = 0
n=2: start=-9/25,endpoint=-27/125,avg=-36/125,residual=9/25 + (1/2)*(-36/125) - 27/125 = 0
```

The finite decay table is:

```text
state       1    3/5   9/25   27/125
ratio            3/5   3/5    3/5
bounds      0 <= state <= 1
```

The checked negative row isolates only the first-step scalar contradiction:

```text
crank_nicolson_next_state = 3/5
crank_nicolson_next_state = 1/2
```

That is intentionally small. The pack is a finite exact replay resource, not a
proof of the general Crank-Nicolson method.
