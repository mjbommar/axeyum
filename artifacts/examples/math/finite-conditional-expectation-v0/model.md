# Model

The finite probability space has four equally likely atoms:

```text
P(a) = P(b) = P(c) = P(d) = 1/4
```

The integrable random variable is:

```text
X(a) = 0
X(b) = 2
X(c) = 4
X(d) = 8
```

The conditioning partition is:

```text
low  = {a,b}
high = {c,d}
```

The conditional expectation is constant on each block:

```text
E[X | low]  = (0*(1/4) + 2*(1/4)) / (1/2) = 1
E[X | high] = (4*(1/4) + 8*(1/4)) / (1/2) = 6
```

So the atom table is:

```text
E[X | partition](a) = 1
E[X | partition](b) = 1
E[X | partition](c) = 6
E[X | partition](d) = 6
```

## Total Expectation

The checker recomputes:

```text
E[X] = 0*(1/4) + 2*(1/4) + 4*(1/4) + 8*(1/4) = 7/2
E[E[X | partition]] = 1*(1/2) + 6*(1/2) = 7/2
```

The false total-expectation row keeps the same conditional-expectation table
but asserts `E[E[X | partition]] = 4`. The checked linear contradiction is:

```text
source_expectation = 7/2
conditional_expectation_expectation = source_expectation
conditional_expectation_expectation = 4
```

## Tower Property

For the coarser partition `{a,b,c,d}`, the checker recomputes:

```text
E[E[X | low/high] | all] = 7/2 = E[X | all]
```

## Bad Conditional Expectation Claim

The false claim says the high block conditional expectation is `5`. The checker
rejects it because the exact high-block weighted average is `6`.

The final linear contradiction is:

```text
(1/2)*high_block_expectation = 3
high_block_expectation = 5
```

The pack keeps this contradiction on the checked `UnsatFarkas` route.

## Bad Tower Claim

The false tower-property claim says the coarse-block value of
`E[E[X | low/high] | all]` is `4`. The checker rejects it because exact
nested-partition replay computes:

```text
E[E[X | low/high] | all] = 1*(1/4) + 1*(1/4) + 6*(1/4) + 6*(1/4) = 7/2
```

The final linear contradiction is:

```text
tower_value = 7/2
tower_value = 4
```

The pack keeps this contradiction on the checked `UnsatFarkas` route.
