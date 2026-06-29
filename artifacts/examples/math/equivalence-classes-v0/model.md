# Model

An equivalence relation is a finite relation `R` over a carrier `E`:

```text
reflexive:  for every x in E, (x, x) in R
symmetric:  if (x, y) in R, then (y, x) in R
transitive: if (x, y) and (y, z) are in R, then (x, z) in R
```

The checker computes the equivalence class of each element as:

```text
[x] = { y in E | (x, y) in R }
```

and compares the distinct classes against the pack's listed class table.

A partition is represented as named blocks. The checker requires every element
to appear in exactly one block, then induces the relation:

```text
x ~ y iff x and y are in the same block
```

A quotient map is a finite function from elements to class labels. The checker
recomputes fibers and checks:

```text
x ~ y iff q(x) = q(y)
```

The Axeyum target is finite model replay today. The graduation route is a QF_UF
view where equality and congruence conflicts can be certified through the
Alethe proof route.

## Limitations

The pack is a fixed finite artifact. General quotient constructions, quotient
types, choice-dependent representative selection, and infinite-domain
equivalence relations remain proof-assistant material.
