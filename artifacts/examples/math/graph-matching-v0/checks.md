# Checks

## `matching-size-two-witness`

Expected result: `sat`.

The witness lists the path graph `a-b-c-d` and the matching:

```text
(a,b), (c,d)
```

The validator checks that both edges are real graph edges, no endpoint is reused,
all vertices are covered, and no larger matching exists by finite enumeration.

## `overlapping-matching-rejected`

Expected result: `unsat`.

The listed edges:

```text
(a,b), (b,c)
```

share vertex `b`, so they are not a matching. The validator confirms this is a
semantic rejection, not a malformed edge-list rejection.

## `augmenting-path-improves`

Expected result: `sat`.

The current matching is `(b,c)` and the augmenting path is:

```text
a, b, c, d
```

The validator checks unmatched endpoints, alternating edges, and that flipping
the path gives `(a,b), (c,d)`.

## `triangle-no-perfect-matching`

Expected result: `unsat`.

The triangle `K3` has three vertices, so no matching can cover every vertex. The
validator proves the fixed row by enumerating all matchings and confirming the
maximum size is `1`.

The promoted solver artifact is:

```text
artifacts/examples/math/graph-matching-v0/cnf/triangle-no-perfect-matching.cnf
```

It uses one Boolean variable per edge of `K3`. Three clauses require every
vertex to be covered by a selected edge, and three clauses require every vertex
to be covered by at most one selected edge. The shared Boolean regression:

```text
crates/axeyum-cnf/tests/math_resource_boolean_routes.rs::graph_matching_triangle_no_perfect_matching_emits_checked_drat_and_lrat
```

parses the DIMACS artifact, emits a DRAT refutation, elaborates it to LRAT, and
checks both proof objects independently.
