# Model

The factor spaces are a fair coin and a fair three-sided die:

```text
P(heads) = 1/2
P(tails) = 1/2

Q(one) = 1/3
Q(two) = 1/3
Q(three) = 1/3
```

The product space has six atoms, each with probability `1/6`:

```text
(heads, one)   (heads, two)   (heads, three)
(tails, one)   (tails, two)   (tails, three)
```

The rectangle `{heads} x {two, three}` has product measure:

```text
P({heads}) * Q({two, three}) = (1/2) * (2/3) = 1/3
```

## Marginals

The checker recomputes marginals by summing the product table:

```text
sum_y R(heads, y) = 1/2
sum_y R(tails, y) = 1/2

sum_x R(x, one) = 1/3
sum_x R(x, two) = 1/3
sum_x R(x, three) = 1/3
```

## Finite Fubini

The simple function is:

```text
f(heads, one) = 1    f(heads, two) = 2    f(heads, three) = 3
f(tails, one) = 2    f(tails, two) = 4    f(tails, three) = 6
```

The validator recomputes the direct finite integral and both iterated sums:

```text
sum_(x,y) f(x,y) R(x,y) = 3
sum_x P(x) * sum_y f(x,y) Q(y) = 3
sum_y Q(y) * sum_x f(x,y) P(x) = 3
```

## Bad Product Claim

The false claim says `R(heads, one) = 1/5`. The checker rejects it because the
exact product probability is `(1/2) * (1/3) = 1/6`.
