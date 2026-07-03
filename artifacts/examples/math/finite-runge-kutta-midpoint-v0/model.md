# Model

The model is a fixed exact-rational explicit midpoint calculation.

```text
ODE: y' = 2t
initial condition: y(0) = 0
step size: h = 1/2
exact solution: y(t) = t^2
```

For each step:

```text
k1 = 2*t_n
t_mid = t_n + 1/4
y_mid = y_n + (1/4)*k1
k2 = 2*t_mid
y_(n+1) = y_n + (1/2)*k2
```

The listed finite trace is:

| n | t_n | y_n | k1 | t_mid | y_mid | k2 | y_(n+1) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 | 1/4 | 0 | 1/2 | 1/4 |
| 1 | 1/2 | 1/4 | 1 | 3/4 | 1/2 | 3/2 | 1 |
| 2 | 1 | 1 | 2 | 5/4 | 3/2 | 5/2 | 9/4 |

The exact-solution and error table is:

| t | listed state | exact t^2 | absolute error |
|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 |
| 1/2 | 1/4 | 1/4 | 0 |
| 1 | 1 | 1 | 0 |
| 3/2 | 9/4 | 9/4 | 0 |

This finite zero-error table is a special property of this fixed problem and
grid. It is not a general Runge-Kutta convergence or order theorem.
