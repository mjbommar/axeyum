# Model

Graphs are finite, undirected, simple graphs:

```text
G = (V, E)
V = listed vertex strings
E = listed unordered vertex pairs
```

Traversal order is deterministic because the validator uses the listed vertex
order as the neighbor order. For the main witness:

```text
vertices = s, a, b, c, d, t
edges = (s,a), (a,b), (b,c), (c,d), (d,t), (s,t)
```

BFS from `s` finds the direct target edge:

```text
path = s, t
distance = 1
```

DFS with the same vertex order walks the long tail first:

```text
order = s, a, b, c, d, t
```

This is a bounded witness for a traversal-pathology lesson: a finite DFS trace
can do more work than the shortest-path distance, even though both procedures
are replayable on the same graph.

The no-path and edge-cut rows use smaller fixed graphs. They are checked by
recomputing reachability, not by trusting the prose.

For the promoted disconnected no-path row, the CNF model uses the four vertices:

```text
s, a, b, t
```

and the two undirected edges:

```text
(s,a), (b,t)
```

The Boolean variable `r_i_v` means that `v` is reachable from `s` in at most
`i` steps. The artifact fixes depth `0` to only `s`, then each later depth is
defined from the previous depth and the graph's neighbor relation. The final
assertion `r_3_t` contradicts those equations. Depth `3` is enough because a
simple path in a four-vertex graph never needs more than three edges.
