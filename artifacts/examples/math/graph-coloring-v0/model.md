# Model

A finite graph is represented by:

- `vertices`: unique string vertex identifiers;
- `edges`: unordered two-element vertex pairs;
- `colors`: unique string color identifiers;
- `assignment`: a map from every vertex to one listed color.

Example:

```json
{
  "vertices": ["a", "b", "c"],
  "edges": [["a", "b"], ["b", "c"], ["a", "c"]],
  "colors": ["red", "green", "blue"],
  "assignment": {
    "a": "red",
    "b": "green",
    "c": "blue"
  }
}
```

Edges are undirected and self-loops are rejected. A proper coloring assigns one
listed color to every vertex and gives different colors to the endpoints of
every edge.

## Checks

### Triangle 3-Coloring

The triangle `K3` has a proper 3-coloring:

```text
a -> red
b -> green
c -> blue
```

### Bad Edge Coloring

The graph with one edge `u--v` is not properly colored when both endpoints are
assigned `red`.

### Triangle Not 2-Colorable

The validator enumerates every assignment of two colors to the three vertices
of `K3` and confirms that every assignment leaves at least one monochromatic
edge.

These fixed checks are not general graph theory proofs. They are small,
deterministic finite examples that should later graduate to generated CNF and
checked SAT proof artifacts.
