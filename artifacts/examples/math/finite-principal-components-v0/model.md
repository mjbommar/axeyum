# Model

## Fixed Sample

The pack fixes four rational observations:

```text
x1 = (-2,  0)
x2 = ( 2,  0)
x3 = ( 0, -1)
x4 = ( 0,  1)
```

The exact mean is:

```text
mu = (0, 0)
```

So the centered rows are the sample rows themselves.

## Covariance

The centered Gram matrix is:

```text
X^T X =
  [ 8  0 ]
  [ 0  2 ]
```

Using the population denominator `4`, the covariance matrix is:

```text
C =
  [ 2    0 ]
  [ 0  1/2 ]
```

The total variance is the trace:

```text
trace(C) = 5/2
```

## Principal Component

The principal vector and eigenvalue are:

```text
v1 = (1, 0)
lambda1 = 2
C v1 = (2, 0) = lambda1 v1
```

The secondary vector and eigenvalue are:

```text
v2 = (0, 1)
lambda2 = 1/2
C v2 = (0, 1/2) = lambda2 v2
```

The principal projected scores are:

```text
[-2, 2, 0, 0]
```

The one-component reconstruction keeps only the first coordinate:

```text
(-2, 0)
( 2, 0)
( 0, 0)
( 0, 0)
```

The residual rows are:

```text
(0,  0)
(0,  0)
(0, -1)
(0,  1)
```

The principal sum of squares is `8`, the residual sum of squares is `2`, and
the explained-variance ratio is:

```text
2 / (5/2) = 4/5
```

## Checked Conflict

The malformed row claims `lambda1 = 3/2`. The source SMT-LIB artifact isolates
the linear contradiction:

```text
vx = 1
2 * vx = lambda
lambda = 3/2
```

That row is checked by the QF_LRA/Farkas route.
