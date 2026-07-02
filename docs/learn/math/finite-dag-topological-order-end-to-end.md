# Finite DAG Topological Order Certificates

This lesson follows
[finite-dag-topological-order-v0](../../../artifacts/examples/math/finite-dag-topological-order-v0/).
It is about one finite directed graph and one finite cycle, not about proving a
general topological-sort algorithm.

## What Is Checked

The finite DAG is:

```text
intro -> algebra
intro -> analysis
algebra -> topology
analysis -> topology
topology -> thesis
```

The checker accepts an order only when:

1. every vertex appears exactly once;
2. every directed edge goes from an earlier vertex to a later vertex.

Two orders check:

```text
intro, algebra, analysis, topology, thesis
intro, analysis, algebra, topology, thesis
```

The second order is valid because `algebra` and `analysis` are incomparable in
the listed graph.

## The Bad Order

The malformed row claims this is topological:

```text
intro, topology, algebra, analysis, thesis
```

The checker rejects it because the edge:

```text
algebra -> topology
```

points backward in that order.

## The Cycle Obstruction

The cyclic graph is:

```text
a -> b -> c -> a
```

The checker replays the cycle:

```text
a, b, c, a
```

Any total order of `a`, `b`, and `c` places one of those cycle edges backward,
so the finite topological-order claim is rejected.

## Trust Boundary

This is the DAG version of Axeyum's resource pattern:

```text
untrusted fast search -> candidate order or cycle
trusted small checking -> vertex coverage, edge positions, and cycle replay
```

The checker does not trust a traversal trace, Kahn queue order, DFS finish
times, or any algorithm implementation. It trusts only the replay of the listed
finite graph and listed finite witness.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-dag-topological-order-v0
```

Expected shape:

```text
validated 1 foundational example pack(s)
```

## What Remains Horizon

The checked rows do not prove the finite linear-extension theorem, Kahn's
algorithm, DFS-based topological sort, cycle-detection completeness,
partial-order dimension results, or asymptotic runtime. Those remain
Lean/theorem-horizon work until proof artifacts exist.
