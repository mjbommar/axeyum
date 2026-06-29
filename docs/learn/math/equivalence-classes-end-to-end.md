# End To End: Equivalence Classes

This lesson follows one finite equivalence-class resource from relation,
partition, and quotient-map tables to replayed result and proof/evidence
status. It uses the
[equivalence-classes-v0](../../../artifacts/examples/math/equivalence-classes-v0/)
pack.

Concept rows:

- `curriculum_relations_and_functions`, `curriculum_sets`, and
  `curriculum_cardinality` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_set_theory_and_foundations` and `field_discrete_math` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `equivalence-relation-classes-witness` | `sat` | replay-only |
| `quotient-map-fiber-witness` | `sat` | replay-only |
| `partition-relation-roundtrip` | `sat` | replay-only |
| `bad-equivalence-rejected` | `unsat` | checked |
| `qf-uf-congruence-proof-gap` | `not-run` | proof-gap |

The checked rows are finite relation, partition, and quotient-map rows. The
pack does not claim general quotient constructions, quotient types,
choice-dependent representative selection, or infinite-domain equivalence
relations.

## Encode

An equivalence relation is a finite relation over a finite carrier:

```text
reflexive:  for every x, x ~ x
symmetric:  if x ~ y, then y ~ x
transitive: if x ~ y and y ~ z, then x ~ z
```

The checker computes each class directly:

```text
[x] = { y | x ~ y }
```

A partition is a set of named blocks. A quotient map is a finite function from
elements to class labels:

```text
q(x) = label of the block containing x
```

The intended Axeyum graduation route is a QF_UF view where quotient-style
equality and congruence conflicts are certified through Alethe evidence. This
pack currently replays finite tables.

## Replay Same-Parity Classes

The first witness is the same-parity relation on `{0,1,2,3}`:

```text
0 ~ 0, 0 ~ 2
1 ~ 1, 1 ~ 3
2 ~ 0, 2 ~ 2
3 ~ 1, 3 ~ 3
```

The validator checks reflexivity, symmetry, and transitivity. It then
recomputes the distinct classes:

```text
even = {0,2}
odd  = {1,3}
```

The row is accepted only because the listed relation and class table match
exactly.

## Replay The Quotient Map

The quotient-map witness is:

```text
q(0) = even
q(1) = odd
q(2) = even
q(3) = odd
```

The checker first verifies the map is total and single-valued. It then
recomputes fibers:

```text
fiber(even) = {0,2}
fiber(odd)  = {1,3}
```

Finally it checks the defining equivalence:

```text
x ~ y iff q(x) = q(y)
```

For example, `0 ~ 2` and both map to `even`; `0` is not related to `1`, and
their quotient labels differ.

## Replay A Partition Round Trip

The partition witness has blocks:

```text
left   = {a,b}
middle = {c}
right  = {d,e}
```

The checker verifies that every element appears in exactly one block. It then
recomputes the induced relation:

```text
x ~ y iff x and y are in the same block
```

So `a ~ b`, `d ~ e`, and `c` is related only to itself. The row passes because
the induced relation is exactly the listed pair set.

## Check The Non-Transitive Refutation

The bad row lists a relation on `{a,b,c}` with:

```text
a ~ b
b ~ c
```

and the symmetric/reflexive pairs, but it omits:

```text
a ~ c
```

The validator confirms reflexivity and symmetry, then rejects the equivalence
claim because transitivity fails on the triple `(a,b,c)`.

## Keep The Proof Gap Visible

The final row is not a replayed theorem. It records the missing proof-object
route:

```text
QF_UF/Alethe certificate for quotient congruence conflicts
```

Finite table replay is enough for the examples above. Equality-heavy quotient
reasoning should not be called proof-object covered until the Alethe route is
implemented and checked.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/equivalence-classes-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for quotient-shaped finite data:

```text
untrusted fast search -> relation table, partition blocks, quotient map
trusted small checking -> equivalence laws, classes, fibers, round trip, counterexample
```

General quotient types, representative-choice theorems, arbitrary quotient
constructions, and infinite equivalence relations require stronger proof routes
or Lean/mathlib-scale proof support.
