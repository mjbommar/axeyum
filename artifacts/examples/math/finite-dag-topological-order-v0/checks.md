# Checks

## `topological-order-witness`

Replays the order:

```text
intro, algebra, analysis, topology, thesis
```

The checker confirms that every vertex appears exactly once and that each edge
points forward in the order.

## `independent-swap-order-witness`

Replays the order:

```text
intro, analysis, algebra, topology, thesis
```

This also checks because `algebra` and `analysis` are incomparable in the
listed graph.

## `bad-order-rejected`

Rejects the order:

```text
intro, topology, algebra, analysis, thesis
```

The concrete violation is:

```text
algebra -> topology
```

The claimed order puts `topology` before `algebra`.

## `cycle-obstruction-rejected`

Rejects a topological-order claim for:

```text
a -> b -> c -> a
```

The checker replays the directed cycle and confirms that the listed order has a
backward edge.

## `topological-sort-theorem-lean-horizon`

Records the theorem boundary: general linear-extension existence, cycle
obstruction completeness, Kahn/DFS topological-sort correctness, and asymptotic
runtime are not proved by this finite replay row.
