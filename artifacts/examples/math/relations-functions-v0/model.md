# Model

Relations are represented as finite sets of ordered pairs.

For a relation `R` on a carrier `E`, the validator checks:

```text
reflexive:     for every x in E, (x, x) in R
antisymmetric: if (x, y) and (y, x) are in R, then x = y
transitive:    if (x, y) and (y, z) are in R, then (x, z) in R
```

Functions are represented as finite graph tables from a declared domain `D` to a
declared codomain `C`.

```text
total:         every x in D has at least one output
single-valued: every x in D has at most one output
injective:     distinct inputs have distinct outputs
surjective:    every y in C is hit by some x in D
```

The Axeyum encoding target is either a Bool/BV enumeration of pair membership or
an EUF view where function consistency and congruence are discharged by QF_UF.
This pack currently replays the finite table directly.

## Limitations

The checks are fixed finite artifacts. General function spaces, quotient
constructions, choice-dependent existence principles, and infinite-domain
cardinality facts remain Lean-horizon material.
