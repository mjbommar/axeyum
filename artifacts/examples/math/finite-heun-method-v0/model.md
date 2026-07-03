# Model

The finite model is a deterministic exact-rational transition system.

Fixed ODE:

```text
f(t, y) = 2t
y(0) = 0
h = 1/2
```

Heun's method is encoded as:

```text
k1 = f(t_n, y_n)
y_predict = y_n + h*k1
k2 = f(t_n + h, y_predict)
avg = (k1 + k2) / 2
y_(n+1) = y_n + h*avg
```

The witness trace is:

```text
times  = 0, 1/2, 1, 3/2
states = 0, 1/4, 1, 9/4
```

The stage table is:

```text
n=0: k1=0, predictor=0,   endpoint=(1/2), k2=1, avg=1/2, next=1/4
n=1: k1=1, predictor=3/4, endpoint=(1),   k2=2, avg=3/2, next=1
n=2: k1=2, predictor=2,   endpoint=(3/2), k2=3, avg=5/2, next=9/4
```

The exact solution table is:

```text
t        0    1/2   1    3/2
state    0    1/4   1    9/4
exact    0    1/4   1    9/4
error    0    0     0    0
```

The checked negative row isolates only the first-step scalar contradiction:

```text
heun_next_state = 1/4
heun_next_state = 1/2
```

That is intentionally small. The pack is a finite exact replay resource, not a
proof of the general Heun method.
