# Model

The finite model is a deterministic exact-rational two-step transition system.

Fixed ODE:

```text
f(t, y) = 2t
y(0) = 0
h = 1/2
```

The pack uses the exact starter value:

```text
y_1 = (1/2)^2 = 1/4
```

Two-step Adams-Bashforth is encoded as:

```text
slope_n = (3/2)*f(t_n,y_n) - (1/2)*f(t_(n-1),y_(n-1))
y_(n+1) = y_n + h*slope_n
```

The witness trace is:

```text
times       = 0, 1/2, 1, 3/2
states      = 0, 1/4, 1, 9/4
derivatives = 0, 1, 2
```

The multistep table is:

```text
n=1: slope=(3/2)*1 - (1/2)*0 = 3/2
     next=1/4 + (1/2)*(3/2) = 1

n=2: slope=(3/2)*2 - (1/2)*1 = 5/2
     next=1 + (1/2)*(5/2) = 9/4
```

The finite error table is:

```text
exact y=t^2 = 0, 1/4, 1, 9/4
absolute errors = 0, 0, 0, 0
max_error = 0
```

The checked negative row isolates only the first multistep scalar
contradiction:

```text
adams_bashforth_next_state = 1
adams_bashforth_next_state = 3/4
```

That is intentionally small. The pack is a finite exact replay resource, not a
proof of the general Adams-Bashforth method.
