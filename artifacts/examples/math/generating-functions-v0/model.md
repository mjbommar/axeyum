# Model

An ordinary generating function prefix is represented as a finite coefficient
list:

```text
[a0, a1, a2, ...]  ->  a0 + a1*x + a2*x^2 + ...
```

The pack only checks finite prefixes and finite polynomial products.

## Coefficient Extraction

The finite triangular-number prefix

```text
1, 3, 6, 10
```

is represented as:

```text
1 + 3*x + 6*x^2 + 10*x^3
```

The checked coefficient indices `0..3` replay to the same prefix.

## Cauchy Product

The Cauchy product of

```text
(1 + 2*x + x^2) * (1 + x + x^2)
```

has coefficients:

```text
1, 3, 4, 3, 1
```

## Fibonacci Prefix

For the finite prefix

```text
F = 0 + x + x^2 + 2*x^3 + 3*x^4 + 5*x^5 + 8*x^6
```

the product `(1 - x - x^2) * F` has prefix:

```text
0, 1, 0, 0, 0, 0, 0
```

through degree `6`. Terms beyond the finite prefix are not claimed.

## False Product

The product of `[1, 2]` and `[3, 4, 5]` is `[3, 10, 13, 10]`, so the claimed
coefficient `12` at index `2` is rejected.

These rows are exact finite replay targets, not a full generating-function
library.
