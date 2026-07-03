# Finite Model

The committed model is a fixed two-cluster rational dataset:

```text
p0 = (-2, 0), cluster 0
p1 = ( 0, 0), cluster 0
p2 = ( 4, 1), cluster 1
p3 = ( 6, 1), cluster 1
```

Cluster membership is not inferred by this pack. It is part of the finite
object being checked. The replay obligations recompute the consequences of that
assignment exactly.

## Centroids

Cluster 0 has points `(-2,0)` and `(0,0)`, so:

```text
mu0 = ((-2 + 0) / 2, (0 + 0) / 2) = (-1, 0)
```

Cluster 1 has points `(4,1)` and `(6,1)`, so:

```text
mu1 = ((4 + 6) / 2, (1 + 1) / 2) = (5, 1)
```

## Residuals And WCSS

Residuals from assigned centroids are:

```text
p0 - mu0 = (-1, 0)
p1 - mu0 = ( 1, 0)
p2 - mu1 = (-1, 0)
p3 - mu1 = ( 1, 0)
```

The squared distances are all `1`, so:

```text
WCSS(cluster 0) = 2
WCSS(cluster 1) = 2
WCSS(total)     = 4
```

## Total And Between-Cluster Decomposition

The global centroid is:

```text
g = (2, 1/2)
```

Total squared deviations from `g` are:

```text
||p0 - g||^2 = 65/4
||p1 - g||^2 = 17/4
||p2 - g||^2 = 17/4
||p3 - g||^2 = 65/4
```

So total squared deviation is `41`.

The cluster-centroid deviations from `g` have squared lengths:

```text
||mu0 - g||^2 = 37/4
||mu1 - g||^2 = 37/4
```

Weighted by cluster sizes, the between-cluster sum-of-squares is:

```text
2 * 37/4 + 2 * 37/4 = 37
```

The finite decomposition is therefore:

```text
total = within + between = 4 + 37 = 41
```

## Bad Row

The malformed replay row claims:

```text
c0x = -1/2
```

But the exact centroid equation gives:

```text
2 * c0x = -2
```

Together, those equalities are inconsistent. The source SMT-LIB artifact
isolates that QF_LRA conflict for the checked Farkas route.
