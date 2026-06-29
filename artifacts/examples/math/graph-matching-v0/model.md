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
