# Group Action Theorem Boundary

This page separates Axeyum's finite group-action resource from general
group-action, orbit-stabilizer, Burnside/Cauchy-Frobenius, quotient-action, and
representation-theory claims.

Primary pack:

- [finite-group-actions-v0](../../../artifacts/examples/math/finite-group-actions-v0/)

Companion lessons and maps:

- [End To End: Finite Group Actions And Burnside Counting](finite-group-actions-end-to-end.md)
- [Algebra And Number Theory](algebra-and-number-theory.md)
- [Sets, Relations, And Finite Structures](sets-relations-and-finite-structures.md)
- [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md)
- [Algebra Equality Certificate Boundary](algebra-equality-certificate-boundary.md)
- [Finite Permutation Groups](finite-permutation-groups-end-to-end.md)
- [Cardinality Theorem Boundary](cardinality-theorem-boundary.md)

## Current Finite Resource

The pack works over a fixed action of `C2 = {e,s}` on the four two-bit strings:

```text
points = 00, 01, 10, 11

e.00 = 00
e.01 = 01
e.10 = 10
e.11 = 11

s.00 = 00
s.01 = 10
s.10 = 01
s.11 = 11
```

The checker recomputes the action laws over the whole finite table:

```text
e.x = x
(g*h).x = g.(h.x)
```

For the sample point `01`, it also recomputes the orbit and stabilizer:

```text
orbit(01) = {01, 10}
stabilizer(01) = {e}
|orbit(01)| * |stabilizer(01)| = 2 * 1 = 2 = |C2|
```

For Burnside-style counting, it recomputes fixed-point counts:

```text
fixed(e) = 4
fixed(s) = 2
(fixed(e) + fixed(s)) / |C2| = 3
orbits = {00}, {01,10}, {11}
```

This is finite table replay. It is useful algebra and counting evidence, but
it does not prove orbit-stabilizer or Burnside/Cauchy-Frobenius for arbitrary
groups.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `c2-swap-action-laws` | `sat` | checked | The fixed finite action table satisfies identity and compatibility laws. |
| `orbit-stabilizer-replay` | `sat` | checked | The orbit and stabilizer of `01` are recomputed from the finite action table. |
| `burnside-orbit-count-replay` | `sat` | checked | The fixed-point average and direct orbit enumeration both give three orbits. |
| `bad-action-rejected` | `unsat` | replay-only | Exact finite replay rejects a malformed identity-action table. |
| `qf-uf-bad-identity-action` | `unsat` | checked | A QF_UF/Alethe row checks the isolated identity-action equality conflict. |
| `bad-compatibility-rejected` | `unsat` | replay-only | Exact finite replay rejects a malformed compatibility table. |
| `qf-uf-bad-action-compatibility` | `unsat` | checked | A QF_UF/Alethe row checks the isolated action-compatibility equality conflict. |
| `general-group-action-theory-lean-horizon` | `not-run` | lean-horizon | General group-action theory remains future proof-assistant work. |

The checked QF_UF/Alethe rows own only the small equality conflicts after
finite replay identifies the failing entry. They do not certify arbitrary
group-action theorem schemas.

## Bad Identity Boundary

The malformed identity row changes one entry:

```text
e.01 = 10
```

The finite checker rejects it because identity action requires:

```text
e.01 = 01
```

The checked QF_UF/Alethe row isolates that final conflict. This is a certificate
for one fixed bad table, not a proof that every action of every group has
identity action.

## Bad Compatibility Boundary

The malformed compatibility row keeps `e` correct but changes the `s` table:

```text
s.01 = 10
s.10 = 10
```

At `g = s`, `h = s`, and `x = 01`, replay computes:

```text
s.(s.01) = s.10 = 10
(s*s).01 = e.01 = 01
```

The checked QF_UF/Alethe row isolates that equality conflict. The trusted route
is still the small finite table plus one proof-object check.

## What Is Not Proved Yet

The current finite group-action resource does not prove:

- orbit-stabilizer for arbitrary group actions;
- Burnside/Cauchy-Frobenius in full generality;
- stabilizers as subgroups in arbitrary settings;
- quotient actions, induced actions, or action transport;
- Cayley's theorem, Sylow actions, class equations, or conjugation-action
  theorems;
- representation-theoretic constructions or character theory;
- group actions on algebraic, topological, measurable, or geometric objects;
- asymptotic enumeration, Polya counting, or large combinatorial species
  claims.

Those claims need precise theorem statements, explicit hypotheses, no-`sorry`
Lean artifacts, and an axiom audit before they can graduate from horizon rows.

## Query The Boundary

Find the group-action horizon row and its finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-group-actions-v0 \
  --require-any
```

Find group-action theorem horizons by text:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text group-action \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-group-actions-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find checked finite QF_UF/Alethe shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-group-actions-v0 \
  --route Alethe \
  --proof-status checked \
  --require-any
```

Drill into the two malformed finite claims separately:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-group-actions-v0 \
  --route Alethe \
  --proof-status checked \
  --text identity \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-group-actions-v0 \
  --route Alethe \
  --proof-status checked \
  --text compatibility \
  --require-any
```

## Graduation Criteria

General group-action resources graduate only when they add:

1. precise Lean theorem statements for identity action, compatibility,
   stabilizer subgroups, orbit-stabilizer, Burnside/Cauchy-Frobenius, quotient
   actions, and induced actions;
2. explicit hypotheses for groups, finite groups, actions, fixed points,
   stabilizers, orbits, quotient sets, and transported structure;
3. no-`sorry` proofs with an axiom audit;
4. links from finite table packs to theorem statements as examples, not as
   proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_UF/Alethe evidence, and
   theorem rows separate.

Until then, group-action rows remain bounded/computable resources:

```text
untrusted fast search -> candidate action table, orbit, stabilizer, fixed counts, or malformed equality
trusted small checking -> finite table replay plus QF_UF/Alethe equality evidence
theorem horizon       -> orbit-stabilizer, Burnside/Cauchy-Frobenius, quotient actions, and representation theory
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-group-actions-v0
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-group-actions-v0 --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-group-actions-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-group-actions-v0 --route Alethe --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
group-action-theory row remains `lean-horizon`.
