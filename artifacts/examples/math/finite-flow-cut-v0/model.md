# Model

The network is a directed graph with source `s`, sink `t`, exact rational edge
capacities, and exact rational edge flows.

```text
s -> a  capacity 2  flow 2
s -> b  capacity 1  flow 1
a -> b  capacity 1  flow 1
a -> t  capacity 1  flow 1
b -> t  capacity 2  flow 2
```

The flow value is `3`. Conservation holds at the internal vertices:

```text
a: inflow 2, outflow 2
b: inflow 2, outflow 2
```

The source-side cut `{s}` has crossing edges `s -> a` and `s -> b`, so its
capacity is `2 + 1 = 3`. Since the feasible flow also has value `3`, this cut
certifies optimality for this fixed network.

The malformed rows are deliberately small:

- `bad-capacity-bound-rejected` changes `flow(s,a)` to `3`, exceeding capacity
  `2`.
- `bad-flow-value-rejected` claims a feasible flow value `4`, but the cut
  `{s}` has capacity `3`.
- `qf-lra-bad-flow-value-cut-bound` keeps the same cut-capacity replay and
  checks the final `4 <= 3` contradiction with source-linked Farkas evidence.

The pack does not prove max-flow/min-cut for arbitrary finite networks,
integrality, Ford-Fulkerson correctness, Edmonds-Karp complexity, or min-cost
flow duality.
