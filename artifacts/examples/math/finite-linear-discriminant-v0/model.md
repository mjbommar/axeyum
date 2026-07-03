# Model

The finite model has two classes in `Q^2`.

Class `A`:

```text
a0 = [0, 0]
a1 = [2, 0]
mu_A = [1, 0]
```

Class `B`:

```text
b0 = [1, 2]
b1 = [1, 4]
mu_B = [1, 3]
```

The centered rows are:

```text
A - mu_A = [[-1, 0], [1, 0]]
B - mu_B = [[0, -1], [0, 1]]
```

The within-class scatter matrices are:

```text
S_A = [[2, 0], [0, 0]]
S_B = [[0, 0], [0, 2]]
S_w = S_A + S_B = [[2, 0], [0, 2]]
```

The mean difference is:

```text
d = mu_B - mu_A = [0, 3]
```

The fixed Fisher direction solves:

```text
S_w w = d
w = [0, 3/2]
```

Projected class means and finite scores are exact rationals:

```text
w . mu_A = 0
w . mu_B = 9/2
threshold = (0 + 9/2) / 2 = 9/4

scores(A) = [0, 0]
scores(B) = [3, 6]
margins(A) = [9/4, 9/4]
margins(B) = [3/4, 15/4]
minimum_margin = 3/4
```

The finite Fisher ratio row records:

```text
(w . d)^2 = 81/4
w . S_w w = 9/2
ratio = 9/2
```

The checked malformed row isolates the linear contradiction:

```text
2*wx = 0
2*wy = 3
wy = 1
```

The contradiction is intentionally tiny. The exact finite replay computes the
sample statistics and direction first; the source SMT-LIB artifact only checks
the final bad-direction equality conflict.
