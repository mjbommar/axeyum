# Model

A ridge regression instance is represented by:

```text
X beta ~= y
```

with exact rational design matrix `X`, response vector `y`, coefficient vector
`beta`, and regularization parameter `lambda`. This pack uses the simple finite
objective:

```text
||y - X beta||^2 + lambda * ||beta||^2
```

The regularized normal equations are:

```text
(X^T X + lambda I) beta = X^T y
```

Residuals use:

```text
r = y - X beta
```

## Fixed Data

The design matrix and response vector are the same tiny regression table used
by the ordinary least-squares pack:

```text
X = [[1,0],
     [1,1],
     [1,2]]
y = [1,2,4]
lambda = 1
```

Then:

```text
X^T X = [[3,3],
         [3,5]]

X^T y = [7,10]

X^T X + I = [[4,3],
             [3,6]]
```

The exact ridge coefficients are:

```text
beta = [4/5, 19/15]
```

They satisfy:

```text
4*(4/5) + 3*(19/15) = 7
3*(4/5) + 6*(19/15) = 10
```

## Residual And Objective

The fitted values and residuals are:

```text
fitted = [4/5, 31/15, 10/3]
residuals = [1/5, -1/15, 2/3]
```

The residual sum of squares is:

```text
RSS = 22/45
```

The coefficient penalty is:

```text
||beta||^2 = 101/45
```

So the ridge objective is:

```text
22/45 + 101/45 = 41/15
```

For comparison, the ordinary least-squares coefficients from the adjacent pack
are `[5/6, 3/2]`. Under the ridge objective they have objective `28/9`, so the
ridge coefficients improve the regularized objective by:

```text
28/9 - 41/15 = 17/45
```

## False Coefficient

The bad row claims:

```text
beta0 = 1
```

Together with the regularized normal equations:

```text
4*beta0 + 3*beta1 = 7
3*beta0 + 6*beta1 = 10
```

this is inconsistent. The exact replay computes `beta0 = 4/5`, while the
source SMT-LIB artifact keeps the final linear conflict on the checked
`UnsatFarkas` route.
