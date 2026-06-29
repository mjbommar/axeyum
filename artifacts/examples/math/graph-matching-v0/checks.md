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
