# Model

The pack uses the square inscribed in the unit circle centered at the origin:

```text
A = ( 1,  0)
B = ( 0,  1)
C = (-1,  0)
D = ( 0, -1)
```

Every point has squared radius `1`:

```text
|A|^2 = |B|^2 = |C|^2 = |D|^2 = 1
```

The diagonals are `AC` and `BD`. Their midpoints are both the origin:

```text
midpoint(A,C) = ((1 + -1)/2, (0 + 0)/2) = (0,0)
midpoint(B,D) = ((0 + 0)/2, (1 + -1)/2) = (0,0)
```

The diagonal directions are:

```text
C - A = (-2,0)
D - B = (0,-2)
```

Their dot product is zero, so the fixed diagonals are perpendicular.

The angle at `B` uses vectors from `B` to `A` and `C`:

```text
A - B = (1,-1)
C - B = (-1,-1)
(1,-1) . (-1,-1) = 0
```

The angle at `D` uses vectors from `D` to `A` and `C`:

```text
A - D = (1,1)
C - D = (-1,1)
(1,1) . (-1,1) = 0
```

The bad row does not ask the solver to rediscover cyclic geometry. The
validator replays the diagonal midpoint first, then the SMT-LIB artifact checks
only the final exact linear contradiction:

```text
diagonal_intersection_x = 0
diagonal_intersection_x = 1/2
```
