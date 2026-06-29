# Model

The graph is a finite undirected diamond:

```text
s -- a -- t
 \       /
  b ----
```

as data:

```text
vertices = s, a, b, t
edges = (s,a), (a,t), (s,b), (b,t)
```

An edge cut is checked by removing listed edges and recomputing reachability
from `s` to `t`. A partition certificate additionally lists the `s` side and
the `t` side; the validator checks that the cut edges are exactly the crossing
edges.

A vertex cut is checked by removing listed internal vertices, never `s` or `t`,
and recomputing reachability. Minimum-size claims are checked by enumerating all
smaller candidate cuts in this fixed finite graph.
