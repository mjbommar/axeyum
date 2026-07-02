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

The bad convex-combination source row keeps those weights fixed and claims the
same affine combination has x-coordinate `1/2`. Exact replay leaves
x-coordinate error:

```text
1/2 - 1/3 = 1/6
```

The separate checked `qf-lra-bad-convex-combination-point` row owns the fixed
linear contradiction `point_x_error = 1/6` and `point_x_error = 0`.

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

The bad separator source row computes `outside_score = 4` while a malformed
claim requires `outside_score <= 1`; the separate checked
`qf-lra-bad-separator` row owns that fixed linear contradiction.
