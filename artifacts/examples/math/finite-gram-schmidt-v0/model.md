# Model

The finite model uses exact rational arithmetic over two input columns:

```text
a1 = [3,4]
a2 = [1,0]

A = [[3,1],
     [4,0]]
```

The first normalization is:

```text
r11 = 5
q1 = [3/5, 4/5]
```

The projection of `a2` onto `q1` is:

```text
r12 = q1 dot a2 = 3/5
u2 = a2 - r12*q1 = [16/25, -12/25]
```

The second normalization is:

```text
r22 = 4/5
q2 = [4/5, -3/5]
```

The resulting QR replay is:

```text
Q = [[3/5,  4/5],
     [4/5, -3/5]]

R = [[5, 3/5],
     [0, 4/5]]

Q^T*Q = I
Q*R = A
```

The malformed row claims `r12 = 4/5`. Exact replay computes `r12 = 3/5`, and
the source SMT-LIB artifact isolates that scalar contradiction for the Farkas
route.
