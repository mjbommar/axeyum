# End To End: Finite Groups

This lesson follows one finite group resource from a Cayley table to replayed
result and proof/evidence status. It uses the
[finite-groups-v0](../../../artifacts/examples/math/finite-groups-v0/) pack.

Concept rows:

- `curriculum_groups` and `curriculum_relations_and_functions` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_abstract_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `z4-addition-group-table` | `sat` | replay-only |
| `z4-inverse-table` | `sat` | replay-only |
| `subtraction-mod3-non-group` | `unsat` | checked |
| `qf-uf-group-operation-congruence-alethe` | `unsat` | checked |

The first three rows are finite Cayley-table replay rows. The final row is a
concrete QF_UF proof-object check for operation congruence. The pack does not
claim Lagrange's theorem, Sylow theory, classification of finite groups, or
quantified group theory.

## Encode

The positive witness is `Z/4Z` under addition:

```text
carrier = {0, 1, 2, 3}
identity = 0
operation = addition modulo 4
```

The pack stores the operation as a table:

| + | `0` | `1` | `2` | `3` |
|---|---|---|---|---|
| `0` | `0` | `1` | `2` | `3` |
| `1` | `1` | `2` | `3` | `0` |
| `2` | `2` | `3` | `0` | `1` |
| `3` | `3` | `0` | `1` | `2` |

The checker treats this table as untrusted data. It does not trust the label
`Z/4Z`; it checks the table directly.

## Replay The Group Laws

The validator checks the finite group obligations by enumerating the table:

```text
closure:       every table entry is in {0,1,2,3}
identity:      0 + x = x and x + 0 = x
inverse:       for every x, some y has x + y = 0 and y + x = 0
associativity: (x + y) + z = x + (y + z) for all triples
```

For example:

```text
1 + 3 = 0
2 + 2 = 0
(1 + 2) + 3 = 3 + 3 = 2
1 + (2 + 3) = 1 + 1 = 2
```

The row is accepted only because every finite closure, identity, inverse, and
associativity check succeeds.

## Replay The Inverse Table

The pack also lists a complete inverse table:

```text
0 -> 0
1 -> 3
2 -> 2
3 -> 1
```

The checker verifies each entry on both sides:

```text
1 + 3 = 0 and 3 + 1 = 0
2 + 2 = 0 and 2 + 2 = 0
3 + 1 = 0 and 1 + 3 = 0
```

This separates two useful questions: "is this operation a group?" and "does
this candidate inverse table match that operation?"

## Check The Refutation

The bad row uses subtraction modulo `3`:

| - | `0` | `1` | `2` |
|---|---|---|---|
| `0` | `0` | `2` | `1` |
| `1` | `1` | `0` | `2` |
| `2` | `2` | `1` | `0` |

The fixed false claim says this table is a group operation with identity `0`.
It already fails the left-identity requirement:

```text
0 - 1 = 2
```

A two-sided identity would require `0 * 1 = 1`, so the group claim is rejected.

## Check The Operation Congruence Certificate

The proof-object row treats the group operation as a binary uninterpreted
function:

```text
a = b
c = d
mul(a, c) != mul(b, d)
```

The artifact lives at
`artifacts/examples/math/finite-groups-v0/smt2/group-operation-congruence-conflict.smt2`.
The resource regression checks that Axeyum emits `Evidence::UnsatAletheProof`
with the pure EUF Alethe emitter and then rechecks the proof independently.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-groups-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for finite algebra:

```text
untrusted fast search -> candidate Cayley table and inverse table
trusted small checking -> closure, identity, inverses, associativity, counterexample row, Alethe congruence proof
```

General group theory, quotient groups, Sylow theory, representation theory, and
statements quantified over all groups require stronger proof routes or
Lean/mathlib-scale proof support.
