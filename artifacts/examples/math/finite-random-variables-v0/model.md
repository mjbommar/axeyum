# Model

The first finite probability space has three weather atoms:

```text
P(clear) = 1/2
P(rain) = 1/4
P(storm) = 1/4
```

The commute-time random variable is a total finite function:

```text
X(clear) = short
X(rain) = medium
X(storm) = long
```

The pushforward distribution is:

```text
P(X = short) = 1/2
P(X = medium) = 1/4
P(X = long) = 1/4
```

## Expectation

The outcome values are:

```text
short = 10
medium = 20
long = 40
```

The checker recomputes expectation two ways:

```text
E[X] = 10*(1/2) + 20*(1/4) + 40*(1/4) = 20
```

## Independence

The second witness is a fair coin crossed with a fair two-outcome signal:

```text
P(heads, green) = 1/4
P(heads, red) = 1/4
P(tails, green) = 1/4
P(tails, red) = 1/4
```

The checker recomputes the marginal distributions of `Coin` and `Signal`, then
checks each joint probability equals the product of its marginals.

## Bad Pushforward Claim

The false claim says `P(X = long) = 1/2`. The checker rejects it because the
exact pushforward mass for `long` is `1/4`.

The checked proof-object row then isolates the final linear contradiction:

```text
long_probability = 1/4
long_probability = 1/2
```

## Bad Expectation Claim

The false claim says `E[X] = 25`. The checker rejects it because exact source
and pushforward replay both compute:

```text
E[X] = 20
```

The checked proof-object row then isolates the final linear contradiction:

```text
expectation_value = 20
expectation_value = 25
```
