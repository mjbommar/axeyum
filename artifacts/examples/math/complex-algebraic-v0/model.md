# Model

Complex numbers are represented as exact rational pairs:

```text
a + bi  ->  [a, b]
```

For `z = [a, b]` and `w = [c, d]`, the operations are:

```text
z + w = [a + c, b + d]
z * w = [a*c - b*d, a*d + b*c]
conjugate(z) = [a, -b]
norm_squared(z) = a*a + b*b
```

## Arithmetic Witness

For `z = 1 + 2i` and `w = 3 - i`:

```text
z + w = 4 + i
z * w = 5 + 5i
```

## Conjugate Norm Witness

For `z = 3 + 4i`:

```text
conjugate(z) = 3 - 4i
z * conjugate(z) = 25 + 0i
```

The bad norm row reuses the same exact source object but claims:

```text
norm_squared(3 + 4i) = 26
```

Exact replay computes `25`, so the final equality is a small QF_LRA/Farkas
contradiction.

## Polynomial Root Witness

For `z = i`:

```text
z^2 = -1 + 0i
z^2 + 1 = 0 + 0i
```

These examples are fixed algebraic replay targets. They are not general
theorems about complex analysis.
