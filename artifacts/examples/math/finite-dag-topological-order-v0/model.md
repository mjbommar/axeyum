# Model

The DAG is a tiny prerequisite graph:

```text
intro -> algebra
intro -> analysis
algebra -> topology
analysis -> topology
topology -> thesis
```

One valid topological order is:

```text
intro, algebra, analysis, topology, thesis
```

Another valid order swaps the independent middle vertices:

```text
intro, analysis, algebra, topology, thesis
```

For an order to check, every directed edge `u -> v` must put `u` earlier than
`v`.

The bad-order row uses:

```text
intro, topology, algebra, analysis, thesis
```

That violates the edge:

```text
algebra -> topology
```

The `qf-lia-bad-topological-edge-order` row keeps the same violating-edge
replay and checks the final integer contradiction:

```text
algebra_position = 2
topology_position = 1
algebra_position < topology_position
```

The cycle-obstruction row uses:

```text
a -> b -> c -> a
```

Any total order of `a`, `b`, and `c` must place at least one of those directed
cycle edges backward.
