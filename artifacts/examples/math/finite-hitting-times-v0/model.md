# Model

The pack uses this finite absorbing Markov chain:

```text
states = start, middle, hit

P(start, start) = 1/2
P(start, middle) = 1/2
P(start, hit) = 0

P(middle, start) = 0
P(middle, middle) = 1/2
P(middle, hit) = 1/2

P(hit, start) = 0
P(hit, middle) = 0
P(hit, hit) = 1
```

The target set is `{hit}` and the initial state is `start`.

## First-Hit Replay

The validator moves only the mass that has not already hit the target. For the
first four steps:

```text
P(T = 1) = 0
P(T = 2) = 1/4
P(T = 3) = 1/4
P(T = 4) = 3/16
P(T > 4) = 5/16
```

These values account for total mass:

```text
0 + 1/4 + 1/4 + 3/16 + 5/16 = 1
```

The malformed survival row keeps the same finite trace but claims:

```text
P(T > 4) = 1/4
```

Exact replay computes `5/16`. The separate `qf-lra-bad-survival-mass` row
checks the final equality conflict through QF_LRA/Farkas evidence.

## Absorption Probability

The listed absorption probabilities are:

```text
p(start) = p(middle) = p(hit) = 1
```

The checker verifies:

```text
p(hit) = 1
p(start) = 1/2*p(start) + 1/2*p(middle)
p(middle) = 1/2*p(middle) + 1/2*p(hit)
```

## Expected Hitting Time

The listed expected hitting times are:

```text
h(hit) = 0
h(middle) = 2
h(start) = 4
```

The checker verifies:

```text
h(start) = 1 + 1/2*h(start) + 1/2*h(middle)
h(middle) = 1 + 1/2*h(middle) + 1/2*h(hit)
```

## Bad Expected-Time Table

The malformed table sets `h(start) = 3`. The checker rejects it because the
right side of the start equation is:

```text
1 + 1/2*3 + 1/2*2 = 7/2
```

which does not equal `3`.

Clearing denominators gives the linear equation:

```text
2*h(start) = 2 + h(start) + h(middle)
```

With `h(start) = 3` and `h(middle) = 2`, that equation reduces to `6 = 7`.
The separate `qf-lra-bad-expected-time` row keeps this final contradiction on
the checked `UnsatFarkas` route.
