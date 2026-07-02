# Model

## Ordered Shortcut-Tail Graph

The base graph is:

```text
vertices = s, a1, a2, a3, a4, t
edges = s-a1, s-t, a1-a2, a2-a3, a3-a4
source = s
target = t
```

The vertex order is part of the deterministic traversal contract. At `s`, DFS
tries `a1` before `t`, so it follows the tail before reaching the shortcut
target.

## BFS Cost

BFS pops vertices in this order until `t` is reached:

```text
s, a1, t
```

The checker verifies distance `1` and `visited_until_target = 3`.

## DFS Cost

DFS preorder reaches the target only after traversing the tail:

```text
s, a1, a2, a3, a4, t
```

The checker verifies `visited_until_target = 6`, even though the shortest
distance remains `1`.

## Bad Bound LIA Artifact

The promoted negative row extracts the length-four graph's cost counters into a
minimal integer contradiction:

```text
dfs_visits = 6
claimed_upper_bound = 3
dfs_visits <= claimed_upper_bound
```

The graph replay justifies the constants. The SMT-LIB artifact then exercises
Axeyum's checked `QF_LIA` arithmetic evidence route for the false cost bound.

## Family Rows

For tail lengths `2, 4, 8`, the generated graph has:

```text
vertices = s, a1, ..., an, t
edges = s-a1, s-t, a1-a2, ..., a(n-1)-an
```

BFS reaches `t` after popping `3` vertices. DFS reaches `t` after popping
`n + 2` vertices.
