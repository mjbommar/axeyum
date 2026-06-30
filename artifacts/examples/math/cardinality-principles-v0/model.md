# Model

The pack models cardinality principles as finite set and incidence tables.

For inclusion-exclusion:

```text
A = {a,b,c}
B = {b,c,d}
A union B = {a,b,c,d}
A intersect B = {b,c}
```

The validator checks `4 = 3 + 3 - 2`.

For disjoint-union additivity, the validator checks that the parts have empty
intersection before accepting the sum of their sizes.

For double-counting, the validator treats a bipartite graph as a finite
relation:

```text
E subseteq Left x Right
sum left degrees = |E| = sum right degrees
```

For powersets, the validator enumerates every subset of the listed base set and
requires the table to match exactly.

For the promoted overlapping-set conflict, finite replay computes:

```text
|A union B| = 4
|A| + |B| = 6
```

The rejected solver artifact asks those two counts to be equal, giving a tiny
QF_LIA/Diophantine contradiction without claiming any arbitrary-cardinality
theorem.

## Limitations

These examples are fixed finite tables. They teach the executable shape of
cardinality arguments, but they do not certify arbitrary infinite-cardinality
theorems such as Cantor-Schroeder-Bernstein or countability/uncountability
results.
