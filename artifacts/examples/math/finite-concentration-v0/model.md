# Model

## Markov Inequality

The Markov witness uses a nonnegative random variable:

```text
P(low) = 3/4
P(high) = 1/4
X(low) = 0
X(high) = 4
```

The checker recomputes:

```text
E[X] = 1
P(X >= 2) = 1/4
E[X] / 2 = 1/2
```

and checks `1/4 <= 1/2`.

## Chebyshev Inequality

The Chebyshev witness uses:

```text
P(left) = 1/4
P(center) = 1/2
P(right) = 1/4
Y(left) = -2
Y(center) = 0
Y(right) = 2
```

The checker recomputes:

```text
E[Y] = 0
Var(Y) = 2
P(|Y - 0| >= 2) = 1/2
Var(Y) / 2^2 = 1/2
```

## Union Bound

The union-bound witness uses four equal atoms:

```text
A = {a, b}
B = {b, c}
P(A) = 1/2
P(B) = 1/2
P(A union B) = 3/4
```

The checker verifies `3/4 <= 1`.

## Bad Bound

The bad-bound row reuses the Markov table but claims:

```text
P(X >= 2) <= 1/8
```

The checker rejects it because the actual probability is `1/4`.
