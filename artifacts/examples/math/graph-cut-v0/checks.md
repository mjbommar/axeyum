# Checks

## `min-edge-cut-partition-witness`

Expected result: `sat`.

The witness uses partition:

```text
source_side = {s}
target_side = {a,b,t}
cut_edges = (s,a), (s,b)
```

The validator checks that these are exactly the crossing edges, removes them,
confirms `t` is unreachable from `s`, and enumerates all one-edge removals to
prove the cut size is minimal for this graph.

## `one-edge-cut-rejected`

Expected result: `unsat`.

Removing only `(s,a)` does not separate the graph because `s-b-t` remains.

## `min-vertex-cut-witness`

Expected result: `sat`.

The witness removes internal vertices:

```text
cut_vertices = {a,b}
```

The validator checks that neither endpoint is removed, then confirms no
one-vertex internal cut separates `s` from `t`.

## `one-vertex-cut-rejected`

Expected result: `unsat`.

Removing only `a` does not separate the graph because `s-b-t` remains.
