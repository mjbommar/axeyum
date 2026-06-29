# Checks

## `union-intersection-identity`

Expected result: `sat`.

The witness checks the finite distributive identity:

```text
A union (B intersect C) = (A union B) intersect (A union C)
```

The validator recomputes both sides over the listed universe and accepts the row
only when the two sets are equal.

## `subset-transitivity-witness`

Expected result: `sat`.

The witness lists nested finite sets `A subset B subset C`. The validator checks
both premises and the conclusion `A subset C`.

## `distributive-law-counterexample-rejected`

Expected result: `unsat`.

The checked query is the fixed false claim:

```text
A intersect (B union C) = (A intersect B) union C
```

The validator recomputes both sides and confirms that the equality fails for the
listed sets. This is a bounded replay rejection, not a general proof object.
