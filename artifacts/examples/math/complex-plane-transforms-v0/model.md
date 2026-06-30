# Model

Complex numbers are exact rational pairs:

```text
a + bi  ->  [a, b]
```

The pack uses the same operations as `complex-algebraic-v0`, plus exact
division by a nonzero denominator:

```text
(a + bi) / (c + di)
  = [(a*c + b*d) / (c*c + d*d), (b*c - a*d) / (c*c + d*d)]
```

## Unit-Root Cycle

For `i = [0, 1]`:

```text
i^0 = 1
i^1 = i
i^2 = -1
i^3 = -i
i^4 = 1
```

Each of the first four powers has norm-squared `1`.

## Conjugation And Products

For `z = 1 + 2i` and `w = 3 - i`:

```text
z*w = 5 + 5i
conjugate(z*w) = 5 - 5i
conjugate(z) * conjugate(w) = 5 - 5i
```

## Mobius Transform Witness

For the fixed transform

```text
f(z) = (z - 1) / (z + 1)
```

and `z = 2 + i`:

```text
z - 1 = 1 + i
z + 1 = 3 + i
f(z) = 2/5 + 1/5 i
```

The denominator norm-squared is `10`, and the image norm-squared is `1/5`.

## False Square Claim

The unit complex number `i` refutes the claim that every unit complex square
has positive real part:

```text
i^2 = -1 + 0i
```

These are exact finite replay targets, not a general complex-analysis library.
