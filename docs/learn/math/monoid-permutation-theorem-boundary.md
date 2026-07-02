# Monoid And Permutation Theorem Boundary

This page separates Axeyum's finite monoid and finite permutation-group
resources from general semigroup, monoid, permutation-group, and
representation-theory claims.

Primary packs:

- [finite-monoids-v0](../../../artifacts/examples/math/finite-monoids-v0/)
- [finite-permutation-groups-v0](../../../artifacts/examples/math/finite-permutation-groups-v0/)

Companion lessons and maps:

- [End To End: Finite Monoids](finite-monoids-end-to-end.md)
- [End To End: Finite Permutation Groups](finite-permutation-groups-end-to-end.md)
- [Group Action Theorem Boundary](group-action-theorem-boundary.md)
- [Algebra And Number Theory](algebra-and-number-theory.md)
- [Sets, Relations, And Finite Structures](sets-relations-and-finite-structures.md)
- [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md)
- [Algebra Equality Certificate Boundary](algebra-equality-certificate-boundary.md)

## Current Finite Resources

The monoid pack works over all total functions on the two-point set `{0,1}`:

```text
id   : 0 -> 0, 1 -> 1
flip : 0 -> 1, 1 -> 0
zero : 0 -> 0, 1 -> 0
one  : 0 -> 1, 1 -> 1
```

The operation is function composition:

```text
table[f][g] = f after g
```

The checker exhaustively validates closure, identity, associativity,
composition-table agreement, units, and idempotents over the fixed four-element
table. It is useful finite algebra evidence, but it is not a proof of general
semigroup or monoid theory.

The permutation-group pack works over `S3` as bijections of `{1,2,3}`:

```text
S3 = {e, r, r2, s12, s13, s23}
r   = (1 2 3)
r2  = (1 3 2)
s12 = (1 2)
s13 = (1 3)
s23 = (2 3)
```

The checker validates bijectivity, group-table laws, composition-table
agreement, cycle lengths, sign multiplication, and the natural action's
orbit/stabilizer count for point `1`:

```text
orbit(1) = {1, 2, 3}
stabilizer(1) = {e, s23}
|orbit(1)| * |stabilizer(1)| = 3 * 2 = 6 = |S3|
```

This is still finite table replay. It does not prove Cayley's theorem,
conjugacy theory, alternating-group theory, Sylow theory, or representation
theory.

## Claim And Evidence Rows

| Pack | Check | Expected | Evidence Status | What It Means |
|---|---|---|---|---|
| `finite-monoids-v0` | `two-point-transformation-monoid-laws` | `sat` | checked | The fixed four-function table is a monoid with identity `id`. |
| `finite-monoids-v0` | `function-composition-table-replay` | `sat` | checked | The table entries are recomputed from finite function composition. |
| `finite-monoids-v0` | `units-and-idempotents-replay` | `sat` | checked | The units `{id, flip}` and idempotents `{id, zero, one}` are recomputed. |
| `finite-monoids-v0` | `bad-nonassociative-table-rejected` | `unsat` | replay-only | Exact finite replay rejects a malformed associative-monoid claim. |
| `finite-monoids-v0` | `qf-uf-bad-monoid-associativity` | `unsat` | checked | A QF_UF/Alethe row checks the isolated associativity equality conflict. |
| `finite-monoids-v0` | `general-monoid-theory-lean-horizon` | `not-run` | lean-horizon | General semigroup and monoid theory remains future proof-assistant work. |
| `finite-permutation-groups-v0` | `s3-permutation-group-laws` | `sat` | checked | The six listed bijections form `S3` under composition. |
| `finite-permutation-groups-v0` | `permutation-composition-table-replay` | `sat` | checked | The Cayley table is recomputed from point-map composition. |
| `finite-permutation-groups-v0` | `cycle-type-and-sign-replay` | `sat` | checked | Cycle lengths, signs, and sign multiplication are recomputed. |
| `finite-permutation-groups-v0` | `natural-action-orbit-stabilizer` | `sat` | checked | The natural action, orbit, stabilizer, and finite count equation are replayed. |
| `finite-permutation-groups-v0` | `bad-nonbijection-rejected` | `unsat` | replay-only | Exact finite replay rejects a malformed permutation claim. |
| `finite-permutation-groups-v0` | `qf-uf-bad-nonbijection-injectivity` | `unsat` | checked | A QF_UF/Alethe row checks the isolated duplicate-image conflict. |
| `finite-permutation-groups-v0` | `general-permutation-group-theory-lean-horizon` | `not-run` | lean-horizon | General permutation-group theory remains future proof-assistant work. |

The checked QF_UF/Alethe rows own only the small equality conflicts after exact
finite replay identifies the failing table entry or duplicate image. They do
not certify arbitrary associativity, bijection, sign, or permutation-group
theorem schemas.

## Bad Monoid Boundary

The malformed monoid row uses carrier `{e,a,b}` with identity `e` and the
critical table facts:

```text
b*b = a
a*b = a
b*a = b
```

Associativity on the failing triple would require:

```text
(b*b)*b = b*(b*b)
```

Replay computes:

```text
(b*b)*b = a*b = a
b*(b*b) = b*a = b
```

Together with `a != b`, the fixed associativity claim is rejected. The checked
QF_UF/Alethe row isolates that equality contradiction. It is a certificate for
one bad finite table, not a proof of general monoid associativity theorems.

## Bad Permutation Boundary

The malformed permutation row is a total self-map of `{1,2,3}`:

```text
bad(1) = 1
bad(2) = 1
bad(3) = 3
```

Exact replay rejects the map because image `1` has duplicate preimages and
image `2` is missing. The checked QF_UF/Alethe row isolates the final conflict:

```text
bad(1) = bad(2)
bad(1) != bad(2)
```

This proves the fixed malformed injectivity claim impossible. It does not
prove general facts about all finite permutations, all symmetric groups, or
all group actions.

## What Is Not Proved Yet

The current finite monoid and permutation resources do not prove:

- semigroup and monoid theory over arbitrary carriers;
- submonoid, quotient-monoid, free-monoid, and presentation theorems;
- Green's relations or transformation-semigroup theory over arbitrary sets;
- category-theoretic monoid objects or universal properties;
- Cayley's theorem or arbitrary permutation representations;
- conjugacy-class, sign-homomorphism, alternating-group, or normal-subgroup
  theorems over arbitrary finite types;
- Sylow theory, class equations, or group-action classification results;
- representation-theoretic constructions or character theory.

Those claims need precise theorem statements, explicit hypotheses, no-`sorry`
Lean artifacts, and an axiom audit before they can graduate from horizon rows.

## Query The Boundary

Find the monoid horizon row and its finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-monoids-v0 \
  --require-any
```

Find the permutation-group horizon row and its finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-permutation-groups-v0 \
  --require-any
```

Find the explicit Lean-horizon rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-monoids-v0 \
  --proof-status lean-horizon \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-permutation-groups-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find checked QF_UF/Alethe shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-monoids-v0 \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-permutation-groups-v0 \
  --route Alethe \
  --proof-status checked \
  --require-any
```

Drill into the two malformed finite claims separately:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-monoids-v0 \
  --route Alethe \
  --proof-status checked \
  --text associativity \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-permutation-groups-v0 \
  --route Alethe \
  --proof-status checked \
  --text injectivity \
  --require-any
```

## Graduation Criteria

General monoid resources graduate only when they add:

1. precise Lean theorem statements for semigroups, monoids, submonoids,
   quotient monoids, free monoids, presentations, and transformation monoids;
2. explicit hypotheses for carriers, operations, identities, associativity,
   generated substructures, congruences, and quotients;
3. no-`sorry` proofs with an axiom audit;
4. links from finite table packs to theorem statements as examples, not as
   proof evidence for the theorem.

General permutation-group resources graduate only when they add:

1. precise Lean theorem statements for bijections, symmetric groups, signs,
   alternating groups, conjugacy, Cayley embeddings, group actions, and
   representation targets;
2. explicit hypotheses for finite types, group structures, function extensionality,
   orbit/stabilizer data, and quotient actions;
3. no-`sorry` proofs with an axiom audit;
4. display labels that keep finite replay, checked QF_UF/Alethe evidence, and
   theorem rows separate.

Until then, these rows remain bounded/computable resources:

```text
untrusted fast search -> candidate finite functions, operation tables, permutation maps, cycles, signs, or malformed equality
trusted small checking -> finite table replay plus QF_UF/Alethe equality evidence
theorem horizon       -> semigroup/monoid theory, Cayley/conjugacy/Sylow theory, and representation theory
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-monoids-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-permutation-groups-v0
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-monoids-v0 --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-permutation-groups-v0 --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-monoids-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-permutation-groups-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-monoids-v0 --route Alethe --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-permutation-groups-v0 --route Alethe --proof-status checked --require-any
```

Expected resource boundary: both finite packs validate, both `horizon-frontier`
queries show `checked-finite-shadow`, and both general-theory rows remain
`lean-horizon`.
