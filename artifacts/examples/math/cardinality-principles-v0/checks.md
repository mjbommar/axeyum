# Checks

## `inclusion-exclusion-two-sets`

Expected result: `sat`.

The validator checks that the listed `union` and `intersection` match `A union
B` and `A intersect B`, then replays:

```text
|A union B| = |A| + |B| - |A intersect B|
```

## `disjoint-union-additivity`

Expected result: `sat`.

The validator checks that the listed parts are disjoint and that the listed
union is exactly their union, then replays cardinality additivity.

## `double-counting-bipartite-edges`

Expected result: `sat`.

The validator recomputes every left and right degree from the listed bipartite
edge table and checks that both degree sums equal the same edge count.

## `finite-powerset-cardinality`

Expected result: `sat`.

The validator enumerates the powerset of the three-element base set and checks
that the listed subsets are exactly those eight subsets.

## `overlapping-disjoint-additivity-counterexample`

Expected result: `sat`.

The validator accepts this row only because `A` and `B` overlap, the false
disjoint sum is `6`, and the true union count is `4`.

## `cantor-schroeder-bernstein-lean-horizon`

Expected result: `not-run`.

This row records the future theorem-prover target for arbitrary set
cardinality theorems. It is not finite evidence.
