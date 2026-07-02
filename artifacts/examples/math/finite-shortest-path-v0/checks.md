# Checks

## `path-distance-witness`

Replays the listed path `s -> a -> b -> t`. The checker verifies each directed
edge exists and sums the weights exactly:

```text
2 + 1 + 2 = 5
```

## `potential-optimality-witness`

Checks the same path and the potential assignment:

```text
p(s)=0, p(a)=2, p(b)=3, p(t)=5
```

The checker verifies each edge relaxation `p(v) <= p(u)+w(u,v)`. The potential
lower bound equals the path length, so this finite row certifies optimality for
the listed graph only.

## `bad-path-distance-rejected`

Rejects the claim that the path `s -> a -> b -> t` has length `4`. Exact replay
computes length `5`.

## `bad-shorter-distance-rejected`

Rejects the claim that the graph has an `s`-to-`t` path of length at most `4`.
The potential certificate lower-bounds every such path by `5`.

## `shortest-path-theorem-lean-horizon`

Records the theorem boundary: general algorithm correctness, negative-cycle
reasoning, all-pairs variants, and asymptotic runtime are not proved by this
finite replay row.
