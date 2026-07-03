# Model

The model is a fixed finite two-class training set in the rational plane with
two rational query points and a fixed neighbor count.

## Classes

```text
positive -> 1
negative -> 0
```

## Squared Euclidean Distance

For a query point `q = (qx, qy)` and a training point `t = (tx, ty)`:

```text
d2(q, t) = (qx - tx)^2 + (qy - ty)^2
```

Working with squared distances keeps every value rational: the square root in
the ordinary Euclidean distance is irrational in general, but ranking by
`d2` selects the same neighbors because squaring is monotone on nonnegative
values. The checked finite object is exact rational arithmetic over the
committed coordinates. No floating-point tolerance is used.

## Neighbor Selection And Vote

For `k = 3`, the neighbor set of a query is the set of training points with
the three smallest squared distances. Both committed queries have a strict
rank gap:

```text
q1: max neighbor d2 = 2  < 18 = min non-neighbor d2
q2: max neighbor d2 = 5  < 13 = min non-neighbor d2
```

so the neighbor sets are unambiguous and no tie-breaking policy is needed.
The predicted class is the strict majority class among the neighbors.

## Fixed Tables

Query `q1 = (1, 1)`:

```text
d2(q1, t1) = 1 + 1  = 2
d2(q1, t2) = 0 + 1  = 1
d2(q1, t3) = 1 + 0  = 1
d2(q1, t4) = 9 + 9  = 18
d2(q1, t5) = 16 + 9 = 25
d2(q1, t6) = 9 + 16 = 25
neighbors = {t1, t2, t3}, vote 3-0 -> positive
```

Query `q2 = (3, 3)`:

```text
d2(q2, t1) = 9 + 9  = 18
d2(q2, t2) = 4 + 9  = 13
d2(q2, t3) = 9 + 4  = 13
d2(q2, t4) = 1 + 1  = 2
d2(q2, t5) = 4 + 1  = 5
d2(q2, t6) = 1 + 4  = 5
neighbors = {t4, t5, t6}, vote 3-0 -> negative
```
