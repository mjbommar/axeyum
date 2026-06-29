# End To End: Finite Monoids

This lesson follows one finite monoid resource from function tables to replayed
result and proof/evidence status. It uses the
[finite-monoids-v0](../../../artifacts/examples/math/finite-monoids-v0/) pack.

Concept rows:

- `curriculum_groups` and `curriculum_relations_and_functions` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_abstract_algebra`, `field_discrete_math`, and
  `field_set_theory_and_foundations` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `two-point-transformation-monoid-laws` | `sat` | checked |
| `function-composition-table-replay` | `sat` | checked |
| `units-and-idempotents-replay` | `sat` | checked |
| `bad-nonassociative-table-rejected` | `unsat` | checked |
| `general-monoid-theory-lean-horizon` | `not-run` | lean-horizon |

The checked rows are exact finite table replay. The pack does not claim general
semigroup theory, quotient monoids, free monoids, presentations, or Green's
relations for arbitrary monoids.

## Encode

The point set is:

```text
X = {0, 1}
```

The carrier is every total function `X -> X`:

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

The stored table is:

| after | `id` | `flip` | `zero` | `one` |
|---|---|---|---|---|
| `id` | `id` | `flip` | `zero` | `one` |
| `flip` | `flip` | `id` | `one` | `zero` |
| `zero` | `zero` | `zero` | `zero` | `zero` |
| `one` | `one` | `one` | `one` | `one` |

## Replay The Monoid Laws

The checker first validates the table as a finite monoid:

```text
identity:      id*f = f and f*id = f
associativity: (f*g)*h = f*(g*h)
```

It exhaustively checks the four-element table. Closure is also explicit:
every table entry must be one of `id`, `flip`, `zero`, or `one`.

## Replay Composition

The table could satisfy the monoid laws while still failing to match the listed
functions. The composition replay row ties the table back to the original
finite maps.

For example:

```text
(flip after zero)(0) = flip(0) = 1
(flip after zero)(1) = flip(0) = 1
```

That resulting function is `one`, so the table cell `flip * zero` must be
`one`. Likewise:

```text
(zero after flip)(0) = zero(1) = 0
(zero after flip)(1) = zero(0) = 0
```

That resulting function is `zero`, so the table cell `zero * flip` must be
`zero`. The validator repeats this for every pair of functions.

## Replay Units And Idempotents

The checker recomputes the invertible elements:

```text
id * id = id
flip * flip = id
```

So the units are:

```text
{id, flip}
```

It also recomputes the idempotents, where `f*f = f`:

```text
id * id = id
zero * zero = zero
one * one = one
```

So the idempotents are:

```text
{id, zero, one}
```

This explains why a monoid is more general than a group: `zero` and `one` are
closed under the operation, but they are not invertible.

## Check The Refutation

The bad row gives a three-element table with identity `e`:

```text
carrier = {e, a, b}
b*b = a
a*b = a
b*a = b
```

Associativity fails on the listed triple:

```text
(b*b)*b = a*b = a
b*(b*b) = b*a = b
```

Because `a != b`, the fixed claim that this table is an associative monoid is
rejected. The linked `QF_UF` artifact states the three table equalities, the
associativity claim `(b*b)*b = b*(b*b)`, and `a != b`; Axeyum emits and
independently rechecks an `UnsatAletheProof` for the resulting EUF
contradiction.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-monoids-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for finite algebra:

```text
untrusted fast search -> candidate function tables, operation table, units
trusted small checking -> composition replay, identity, associativity, units, idempotents
checked proof object -> QF_UF/Alethe certificate for the bad associativity row
```

General semigroup and monoid theory, free monoids, presentations, quotient
monoids, Green's relations, transformation semigroups over arbitrary sets, and
category-theoretic monoid objects require Lean/mathlib-scale proof support.
