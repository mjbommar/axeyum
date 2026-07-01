# End To End: Finite Group Actions And Burnside Counting

This lesson follows one finite group-action resource from table data to
replayed result and proof/evidence status. It uses the
[finite-group-actions-v0](../../../artifacts/examples/math/finite-group-actions-v0/)
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
| `c2-swap-action-laws` | `sat` | checked |
| `orbit-stabilizer-replay` | `sat` | checked |
| `burnside-orbit-count-replay` | `sat` | checked |
| `bad-action-rejected` | `unsat` | checked |
| `bad-compatibility-rejected` | `unsat` | checked |
| `general-group-action-theory-lean-horizon` | `not-run` | lean-horizon |

The checked rows are finite table replay. The pack does not claim general
orbit-stabilizer or Burnside/Cauchy-Frobenius theorems for arbitrary groups.

## Encode

The acting group is `C2 = {e,s}`:

```text
e*e = e
e*s = s
s*e = s
s*s = e
```

The acted-on set is the four two-bit strings:

```text
00, 01, 10, 11
```

The action table treats each group element as a total function on that finite
set:

```text
e.00 = 00
e.01 = 01
e.10 = 10
e.11 = 11

s.00 = 00
s.01 = 10
s.10 = 01
s.11 = 11
```

The `s` action swaps the middle two strings and fixes `00` and `11`.

## Replay The Action Laws

The checker first confirms that the group table itself is a group. Then it
checks two action obligations over every listed point:

```text
e.x = x
(g*h).x = g.(h.x)
```

For example, at `x = 01`:

```text
(s*s).01 = e.01 = 01
s.(s.01) = s.10 = 01
```

The two sides agree. The validator repeats that finite calculation for every
`g`, `h`, and `x`.

## Replay Orbit And Stabilizer

The witness chooses `01` as the sample point. The checker recomputes:

```text
orbit(01) = {e.01, s.01} = {01, 10}
stabilizer(01) = {g in C2 | g.01 = 01} = {e}
```

Then it checks the finite cardinality equation:

```text
|orbit(01)| * |stabilizer(01)| = 2 * 1 = 2 = |C2|
```

This is a replay of the listed finite table, not a proof of the general theorem
for all group actions.

## Replay Burnside Counting

The checker recomputes fixed points for each group element:

| Element | Fixed Points | Count |
|---|---|---:|
| `e` | `00`, `01`, `10`, `11` | 4 |
| `s` | `00`, `11` | 2 |

The Burnside average gives:

```text
(fixed(e) + fixed(s)) / |C2| = (4 + 2) / 2 = 3
```

The checker also enumerates the action orbits directly:

```text
{00}
{01, 10}
{11}
```

The direct orbit enumeration and the fixed-point average both give `3`.

## Reject Bad Identity Action

The bad-action row changes the identity action:

```text
e.01 = 10
```

That violates the required law `e.x = x`. The checker rejects the malformed
table as an `unsat` claim without needing to search for a better action.

## Reject Bad Compatibility

The bad-compatibility row keeps the identity action intact, but changes the
`s` table so compatibility fails:

```text
s.01 = 10
s.10 = 10
```

At `g = s`, `h = s`, and `x = 01`, the two action-law sides split:

```text
s.(s.01) = s.10 = 10
(s*s).01 = e.01 = 01
```

The finite replay finds that concrete mismatch first. The linked QF_UF/Alethe
artifact then checks the isolated equality conflict
`s.(s.01) = (s*s).01`.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-group-actions-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern in a small algebraic setting:

```text
untrusted fast search -> candidate action table
trusted small checking -> group laws, action laws, orbit/stabilizer, Burnside replay
```

The two checked QF_UF/Alethe rows are certificate checks over small equality
conflicts after finite replay has already identified the malformed table entry.

General group-action theory, stabilizer-subgroup theorems, quotient actions,
Burnside/Cauchy-Frobenius in full generality, representation-theoretic
constructions, and group actions on algebraic or topological structures remain
Lean-horizon material.
