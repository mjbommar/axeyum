# Model

Graphs are finite, undirected, simple graphs:

```text
G = (V, E)
V = listed vertex strings
E = listed unordered vertex pairs
```

A matching is a list of graph edges with no repeated endpoint:

```text
matching = (a,b), (c,d)
```

For the path graph:

```text
vertices = a, b, c, d
edges = (a,b), (b,c), (c,d)
```

the matching `(a,b), (c,d)` covers all vertices and has size `2`. The validator
does not trust the size field; it enumerates every matching of the graph.

An augmenting path is checked relative to a current matching. For the current
matching `(b,c)`, the path:

```text
a, b, c, d
```

starts and ends at unmatched vertices and alternates unmatched, matched,
unmatched edges. Flipping the path yields `(a,b), (c,d)`.

For the promoted `K3` no-perfect-matching row, the CNF model selects graph
edges:

```text
x1 = edge (a,b)
x2 = edge (b,c)
x3 = edge (a,c)
```

Perfect matching is encoded as exact vertex coverage. The positive clauses
require each vertex to be incident to at least one selected edge, while the
negative binary clauses require each vertex to be incident to at most one
selected edge. The six clauses are jointly inconsistent because three vertices
cannot be partitioned into disjoint two-endpoint edges.
