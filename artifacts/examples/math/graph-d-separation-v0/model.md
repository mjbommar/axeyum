# Model

The model is a finite directed acyclic graph:

```text
G = (V, E)
E contains directed edges parent -> child
```

D-separation is checked on paths in the undirected skeleton of the DAG. For each
interior triple on a path:

- a non-collider blocks the path if it is in the conditioning set;
- a collider blocks the path unless it or one of its descendants is in the
  conditioning set.

The chain example:

```text
a -> b -> c
```

has an active path from `a` to `c` when the conditioning set is empty. The same
path is blocked when conditioning on `b`.

For the promoted conditioned-chain row, the CNF model uses four Boolean facts:

```text
path_exists = a-b-c is the selected skeleton path
b_noncollider = b is not a collider on that path
b_conditioned = b is in the conditioning set
path_active = the rejected d-connected claim says the path remains active
```

The blocking rule adds `path_active -> not (b_noncollider and b_conditioned)`.
Together with the four asserted facts this is inconsistent, matching the finite
d-separation replay.

The collider example:

```text
a -> b <- c
b -> d
```

is blocked with no conditioning, but opens when conditioning on `d`, a
descendant of the collider `b`.
