# Model

The connected example is the two-point Sierpinski topology:

```text
U = {0,1}
open_sets = {}, {1}, {0,1}
```

The only clopen subsets are:

```text
{}, {0,1}
```

Since no non-empty proper subset is both open and closed, the checker finds no
open separation of the universe.

## Disconnected Example

The disconnected example is the two-point discrete topology:

```text
U = {a,b}
open_sets = {}, {a}, {b}, {a,b}
```

The separation is:

```text
left = {a}
right = {b}
```

Both sets are non-empty, open, disjoint, and their union is the universe.

## Clopen Witness

In the discrete topology, `{a}` is clopen because `{a}` is open and its
complement `{b}` is also open. The checker uses this as a finite certificate
that the space is disconnected.

## Bad Connectedness Claim

The false claim says the two-point discrete topology is connected. The checker
rejects it by recomputing the non-trivial clopen subset `{a}` and the induced
separation `{a}`, `{b}`.
