# End To End: Finite Permutation Groups

This lesson follows one finite permutation-group resource from point maps to
replayed result and proof/evidence status. It uses the
[finite-permutation-groups-v0](../../../artifacts/examples/math/finite-permutation-groups-v0/)
pack.

Concept rows:

- `curriculum_groups`, `curriculum_relations_and_functions`, and
  `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_abstract_algebra`, `field_discrete_math`, and
  `field_set_theory_and_foundations` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `s3-permutation-group-laws` | `sat` | checked |
| `permutation-composition-table-replay` | `sat` | checked |
| `cycle-type-and-sign-replay` | `sat` | checked |
| `natural-action-orbit-stabilizer` | `sat` | checked |
| `bad-nonbijection-rejected` | `unsat` | replay-only |
| `qf-uf-bad-nonbijection-injectivity` | `unsat` | checked QF_UF/Alethe |
| `general-permutation-group-theory-lean-horizon` | `not-run` | lean-horizon |

The checked rows are finite function-table replay. The pack does not claim
Cayley's theorem, conjugacy theory, alternating-group theory, Sylow theory, or
representation theory for arbitrary groups.

## Encode

The acted-on set is:

```text
X = {1, 2, 3}
```

The carrier is the six permutations of `X`:

```text
S3 = {e, r, r2, s12, s13, s23}
```

Each element is a bijective total map `X -> X`:

```text
e(1)=1,   e(2)=2,   e(3)=3
r(1)=2,   r(2)=3,   r(3)=1
r2(1)=3,  r2(2)=1,  r2(3)=2
s12(1)=2, s12(2)=1, s12(3)=3
s13(1)=3, s13(2)=2, s13(3)=1
s23(1)=1, s23(2)=3, s23(3)=2
```

The table uses row-after-column composition:

```text
table[left][right] = left after right
```

For example:

```text
(r after s23)(1) = r(1) = 2
(r after s23)(2) = r(3) = 1
(r after s23)(3) = r(2) = 3
```

That resulting map swaps `1` and `2`, so the table entry is `s12`.

## Replay The Group Laws

The checker first verifies every listed map is a bijection of `{1,2,3}`. Then
it checks the Cayley table as a finite group table:

```text
identity:      e*g = g and g*e = g
inverses:      every g has h with g*h = e and h*g = e
associativity: (g*h)*k = g*(h*k)
```

These are exhaustive finite checks over the six listed table rows.

## Replay Composition

The group-law table could still be the wrong table for the listed maps, so the
pack has a separate composition replay row. For every pair `left`, `right`, the
checker computes:

```text
point -> left(right(point))
```

It then finds the unique listed permutation with that map and compares the
label with the Cayley-table cell. This ties the algebraic table back to the
original finite-function data.

## Replay Cycle Type And Sign

The checker recomputes cycle lengths:

| Element | Cycle Lengths |
|---|---|
| `e` | `[1, 1, 1]` |
| `r` | `[3]` |
| `r2` | `[3]` |
| `s12` | `[2, 1]` |
| `s13` | `[2, 1]` |
| `s23` | `[2, 1]` |

It also recomputes parity from inversion count in the point order `1, 2, 3`:

```text
sign(e) = even
sign(r) = even
sign(r2) = even
sign(s12) = odd
sign(s13) = odd
sign(s23) = odd
```

Then it checks that the sign map preserves multiplication into the two-element
parity group:

```text
sign(g*h) = sign(g) * sign(h)
```

This is still finite replay. The general sign homomorphism theorem remains a
Lean-horizon claim.

## Replay The Natural Action

Every permutation acts on the same point set by evaluation. The natural action
row reuses the maps as an action table and checks:

```text
e.x = x
(g*h).x = g.(h.x)
```

For the sample point `1`, the checker recomputes:

```text
orbit(1) = {1, 2, 3}
stabilizer(1) = {e, s23}
```

Then it checks the finite orbit-stabilizer count:

```text
|orbit(1)| * |stabilizer(1)| = 3 * 2 = 6 = |S3|
```

## Check The Refutation

The bad row is a total self-map that is not a permutation:

```text
f(1)=1
f(2)=1
f(3)=3
```

The image `1` appears twice and the image `2` is missing. The checker rejects
the fixed claim that this map is a bijection. The linked `QF_UF` artifact
records `bad(1)=1`, `bad(2)=1`, and the fixed distinct-image claim
`bad(1) != bad(2)`; Axeyum emits and independently rechecks an
`UnsatAletheProof` for that equality conflict.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-permutation-groups-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for finite symmetry:

```text
untrusted fast search -> candidate permutation maps, table, cycles, signs
trusted small checking -> bijection, composition, group laws, sign, action replay
checked proof object -> QF_UF/Alethe certificate for the bad injectivity row
```

General permutation-group theory, Cayley's theorem, conjugacy classes, normal
subgroups, alternating groups, Sylow theory, and representation theory require
Lean/mathlib-scale proof support beyond these finite table checks.
