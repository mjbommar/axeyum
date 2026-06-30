# Model

The finite convex set is the triangle with rational vertices:

```text
v0 = (0,0)
v1 = (1,0)
v2 = (0,1)
```

The convex-hull witness uses weights:

```text
w = (1/3, 1/3, 1/3)
sum(w) = 1
sum_i w_i * v_i = (1/3, 1/3)
```

The separator witness uses:

```text
normal = (1,1)
threshold = 1
outside = (2,2)
```

The trusted replay recomputes:

```text
normal . v0 = 0
normal . v1 = 1
normal . v2 = 1
normal . outside = 4
margin = 4 - 1 = 3
```

The tight finite face is represented by vertex indices `1` and `2`.
