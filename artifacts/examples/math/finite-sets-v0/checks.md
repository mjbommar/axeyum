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
listed sets.

The pack also carries
[`cnf/distributive-law-counterexample.cnf`](cnf/distributive-law-counterexample.cnf),
a deterministic DIMACS encoding of the element `c` obstruction:

```text
c notin A
c notin B
c in C
left_c  <=> c in A intersect (B union C)
right_c <=> c in (A intersect B) union C
left_c = right_c
```

The focused regression

```sh
cargo test -p axeyum-cnf --test math_resource_boolean_routes finite_sets_distributive_counterexample_emits_checked_drat_and_lrat
```

parses that CNF, emits a DRAT proof with untrusted search, checks the DRAT proof
independently, elaborates it to LRAT, and checks the LRAT proof independently.
