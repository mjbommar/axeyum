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

For the promoted one-edge non-cut row, the CNF model removes `(s,a)` and keeps:

```text
(a,t), (s,b), (b,t)
```

The Boolean variable `r_i_v` means that `v` is reachable from `s` in at most
`i` steps after removal. The artifact fixes depth `0` to only `s`, defines each
later depth from the previous depth and the remaining neighbor relation, and
then asserts `t` is not reachable by depth `3`. That contradicts the explicit
path `s-b-t`, so the proposed one-edge cut is rejected by a checked CNF proof
route rather than by prose alone.
