# End To End: Finite Specialization Order

This lesson follows one finite topology resource from open-set data to
specialization-preorder replay and a checked `T0` counterexample. It uses
[finite-specialization-order-v0](../../../artifacts/examples/math/finite-specialization-order-v0/).

Concept rows:

- `bridge_finite_specialization_order_replay` and
  `bridge_finite_topology_operator_homeomorphism` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_sets` and `curriculum_relations_and_functions` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_topology`, `field_set_theory_and_foundations`, and
  `field_discrete_math` in the
  [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `specialization-preorder-witness` | `sat` | replay-only |
| `closure-characterization-witness` | `sat` | replay-only |
| `t0-poset-witness` | `sat` | replay-only |
| `bad-t0-antisymmetry-rejected` | `unsat` | checked |
| `general-specialization-order-lean-horizon` | `not-run` | lean-horizon |

Every replay row is finite set-family arithmetic. The checked row is a fixed
QF_UF/Alethe equality contradiction after replay identifies mutual
specialization. The pack does not prove general separation-axiom,
specialization-order, sobriety, or domain-theory theorems.

## Encode The Space

The main witness uses the three-point topology:

```text
U = {a,b,c}
open sets = {}, {a}, {a,b}, {a,b,c}
```

The specialization preorder is defined by open neighborhoods:

```text
x <= y  iff  every open set containing x also contains y
```

The validator enumerates each point pair and recomputes:

```text
a <= a
b <= b, b <= a
c <= c, c <= b, c <= a
```

This is the chain:

```text
c <= b <= a
```

## Check Closures

The same relation can be read from singleton closures:

```text
closure({a}) = {a,b,c}
closure({b}) = {b,c}
closure({c}) = {c}
```

The validator checks:

```text
x <= y  iff  x is in closure({y})
```

For example, `c <= b` because `c` is in `closure({b})`.

## Check The T0 Slice

For this finite space, no two distinct points mutually specialize:

```text
a <= b is false
b <= a is true
b <= c is false
c <= b is true
```

So the specialization preorder is antisymmetric, and the finite space is `T0`.
This is still just one finite replay, not the general theorem connecting `T0`
spaces and specialization partial orders.

## Reject A Bad T0 Claim

The negative row uses the indiscrete two-point topology:

```text
U = {x,y}
open sets = {}, {x,y}
```

The only nonempty open set contains both points, so:

```text
x <= y
y <= x
```

A false `T0`/antisymmetry claim would require:

```text
x = y
```

The source SMT-LIB artifact also asserts:

```text
x != y
```

Axeyum emits `UnsatAletheProof` evidence for that fixed equality conflict, and
`Evidence::check` independently rechecks it.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-specialization-order-v0
cargo test -p axeyum-solver --test math_resource_uf_routes finite_specialization_order_bad_t0_antisymmetry_emits_checked_alethe
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate topology, specialization pairs, or bad T0 row
trusted small checking -> finite open-neighborhood replay and checked Alethe equality proof
remaining horizon -> arbitrary specialization-order topology and separation theorems
```

For first-principles topology axiom replay, read
[End To End: Finite Topology](finite-topology-end-to-end.md). For finite
continuous maps and homeomorphism replay, read
[Finite Continuous Maps](finite-continuous-maps-end-to-end.md).
