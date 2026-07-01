# Model

The base finite kernel maps weather states to commute choices:

```text
source = sunny, rainy
target = walk, bus
K(sunny, walk) = 3/4
K(sunny, bus) = 1/4
K(rainy, walk) = 1/5
K(rainy, bus) = 4/5
```

The checker verifies each row sums to one.

## Pushforward

For source distribution

```text
mu(sunny) = 2/3
mu(rainy) = 1/3
```

the target distribution is:

```text
nu(walk) = (2/3)*(3/4) + (1/3)*(1/5) = 17/30
nu(bus)  = (2/3)*(1/4) + (1/3)*(4/5) = 13/30
```

## Joint Table And Disintegration

The joint table induced by `mu` and `K` is:

```text
P(sunny, walk) = 1/2
P(sunny, bus)  = 1/6
P(rainy, walk) = 1/15
P(rainy, bus)  = 4/15
```

The checker verifies `P(x,y) = mu(x) K(x,y)`, recovers the target marginal,
and recovers the kernel rows by exact division `P(x,y) / mu(x)`.

## Composition

A second kernel maps commute choices to arrival states:

```text
L(walk, early) = 2/3
L(walk, late)  = 1/3
L(bus, early)  = 1/5
L(bus, late)   = 4/5
```

The composed kernel is:

```text
(K;L)(sunny, early) = 3/4*2/3 + 1/4*1/5 = 11/20
(K;L)(sunny, late)  = 9/20
(K;L)(rainy, early) = 1/5*2/3 + 4/5*1/5 = 22/75
(K;L)(rainy, late)  = 53/75
```

## Bad Kernel Row

The false row sets:

```text
K(rainy, walk) = 3/5
K(rainy, bus) = 3/5
```

The checker rejects it because the row sum is `6/5`, not `1`.

## Bad Composition Entry

The false composition row reuses the weather-to-commute kernel `K` and the
commute-to-arrival kernel `L`, but claims:

```text
(K;L)(rainy, early) = 1/3
```

Exact replay computes:

```text
(K;L)(rainy, early) = 1/5*2/3 + 4/5*1/5 = 22/75
```

The final contradictory equality is checked through QF_LRA/Farkas evidence.
