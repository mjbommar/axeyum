# Model

The pack uses a three-point universe:

```text
U = {a,b,c}
```

Every subset of `U` is measurable. The normalized exact-rational measure table
is:

```text
mu({}) = 0
mu({a}) = 1/6
mu({b}) = 1/3
mu({c}) = 1/2
mu({a,b}) = 1/2
mu({a,c}) = 2/3
mu({b,c}) = 5/6
mu({a,b,c}) = 1
```

## Monotonicity

For `A = {a}` and `B = {a,b}`:

```text
B \ A = {b}
mu(B) = mu(A) + mu(B \ A)
1/2 = 1/6 + 1/3
mu(A) <= mu(B)
```

The subset relation and difference event are finite set computations. The
measure identity is exact rational arithmetic.

## Subadditivity

For `A = {a,b}` and `B = {b,c}`:

```text
A union B = {a,b,c}
A intersect B = {b}
mu(A union B) = mu(A) + mu(B) - mu(A intersect B)
1 = 1/2 + 5/6 - 1/3
mu(A union B) <= mu(A) + mu(B)
```

## Bad Subset-Measure Claim

The promoted bad row reuses the monotonicity witness but claims:

```text
mu({a}) = 2/3
```

Exact replay computes:

```text
mu({a}) = 1/6
```

The QF_LRA artifact checks only that final equality conflict:

```text
subset_measure = 1/6
subset_measure = 2/3
```

## Bad Union-Subadditivity Claim

The malformed union row reuses the subadditivity witness but claims:

```text
mu(A union B) = 3/2
```

Exact replay computes:

```text
mu(A) + mu(B) = 1/2 + 5/6 = 4/3
```

The QF_LRA artifact checks only that final inequality conflict:

```text
claimed_union_measure = 3/2
left_measure = 1/2
right_measure = 5/6
claimed_union_measure <= left_measure + right_measure
```

This is a finite table replay target, not a proof of countable additivity,
monotone convergence, dominated convergence, or general measure-space facts.
