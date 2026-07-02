# Model

The finite model uses exact rational arithmetic over:

```text
c = 3/5
s = 4/5

G = [[ 3/5, 4/5],
     [-4/5, 3/5]]

x = [3, 4]
```

The rotation is orthogonal:

```text
G^T*G = I
```

The matrix-vector product zeroes the second coordinate:

```text
G*x = [5, 0]
```

The transpose reconstructs the original vector:

```text
G^T*[5,0] = [3,4]
```

The determinant and norm replay are:

```text
det(G) = 1
||x||^2 = 25
||G*x||^2 = 25
```

The malformed row claims `s = 3/5`. Exact replay computes `s = 4/5`, and the
source SMT-LIB artifact isolates that scalar contradiction for the Farkas
route.
