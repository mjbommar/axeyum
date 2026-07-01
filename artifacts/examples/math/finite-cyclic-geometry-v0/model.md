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

The Ptolemy witness uses a `4 x 3` rectangle centered at the origin:

```text
A = (-2, -3/2)
B = ( 2, -3/2)
C = ( 2,  3/2)
D = (-2,  3/2)
```

Each point has squared radius `25/4`. The side lengths are:

```text
AB = 4
BC = 3
CD = 4
DA = 3
```

Both diagonals have length `5`, so the fixed Ptolemy arithmetic is:

```text
AC * BD = 5 * 5 = 25
AB * CD + BC * DA = 4 * 4 + 3 * 3 = 16 + 9 = 25
```

The bad row does not ask the solver to rediscover cyclic geometry. The
validator replays the diagonal midpoint first, then the SMT-LIB artifact checks
only the final exact linear contradiction:

```text
diagonal_intersection_x = 0
diagonal_intersection_x = 1/2
```

The bad opposite-angle row follows the same trust split. The validator replays
the two vectors at `B`, recomputes the dot product, and the SMT-LIB artifact
checks only the final exact linear contradiction:

```text
angle_b_dot = 0
angle_b_dot = 1
```

The bad Ptolemy row follows the same trust split. The validator replays the
rectangle side and diagonal lengths, recomputes both Ptolemy sides, and the
SMT-LIB artifact checks only the final exact linear contradiction:

```text
ptolemy_rhs = 25
ptolemy_rhs = 24
```
