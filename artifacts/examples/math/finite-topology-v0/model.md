# Model

A finite topology is represented by:

- `universe`: unique point identifiers;
- `open_sets`: a list of subsets of the universe.

Example:

```json
{
  "universe": ["a", "b", "c"],
  "open_sets": [
    [],
    ["a"],
    ["a", "b"],
    ["a", "b", "c"]
  ]
}
```

The validator treats sets as unordered and checks the finite topology axioms.

## Checks

### Topology Axioms

The listed open sets contain the empty set and universe and are closed under
pairwise union and intersection.

### Closure And Interior

For subset `{b}` in the listed topology:

```text
interior({b}) = empty
closure({b}) = {b, c}
```

Closure is computed as `X - interior(X - S)`.

### Metric Ball

The finite metric space has points `p0`, `p1`, `p2` with distances:

```text
d(p0, p1) = 1
d(p1, p2) = 2
d(p0, p2) = 3
```

The open ball centered at `p1` with radius `3/2` is exactly `{p0, p1}`.

These fixed checks do not prove general topology theorems.
