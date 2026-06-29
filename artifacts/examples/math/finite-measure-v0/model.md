# Model

A finite sigma-algebra is represented by:

- `universe`: unique point identifiers;
- `measurable_sets`: a list of subsets of the universe.

Measures are represented as a list from measurable sets to exact rational
strings:

```json
{"set": ["a", "b"], "measure": "1/3"}
```

The validator treats sets as unordered.

## Checks

### Sigma-Algebra Axioms

The universe is partitioned into two atoms:

```text
A = {a, b}
B = {c, d}
```

The measurable sets are:

```text
empty, A, B, A union B
```

The validator checks empty/universe membership, complement closure, and
pairwise union closure.

### Finite Measure Additivity

The finite probability measure is:

```text
mu(empty) = 0
mu(A) = 1/3
mu(B) = 2/3
mu(A union B) = 1
```

The validator checks nonnegativity, normalization, and additivity on disjoint
measurable sets.

### Event Complement

For event `A`, the complement has measure `2/3`, and the two measures sum to
the total measure `1`.

These fixed checks are finite measure-table replay targets. They are not
general measure theory.
