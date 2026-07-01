# End To End: Finite Order Lattices

This lesson follows one finite order/lattice resource from relation and table
data to replayed result and proof/evidence status. It uses the
[finite-order-lattices-v0](../../../artifacts/examples/math/finite-order-lattices-v0/)
pack.

Concept rows:

- `curriculum_sets`, `curriculum_relations_and_functions`, and
  `curriculum_cardinality` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_set_theory_and_foundations`, `field_discrete_math`, and
  `field_logic_and_proof` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `boolean-lattice-poset` | `sat` | replay-only |
| `meet-join-table-replay` | `sat` | replay-only |
| `distributive-lattice-replay` | `sat` | replay-only |
| `monotone-map-fixed-points` | `sat` | replay-only |
| `bad-partial-order-rejected` | `unsat` | checked finite replay |
| `qf-uf-bad-partial-order-antisymmetry` | `unsat` | checked QF_UF/Alethe |
| `bad-top-element-rejected` | `unsat` | checked Bool/CNF/LRAT |
| `general-order-lattice-theory-lean-horizon` | `not-run` | lean-horizon |

The checked rows are finite relation and table replay rows. The pack does not
claim complete-lattice fixed-point theorems, domain theory, Galois
connections, Boolean-algebra representation theorems, or infinite-poset
results.

## Encode

The main witness is the powerset lattice of `{a,b}`, encoded as four elements:

```text
0  = {}
A  = {a}
B  = {b}
AB = {a,b}
```

The order is subset inclusion. The pack lists reflexive pairs plus:

```text
0 <= A
0 <= B
0 <= AB
A <= AB
B <= AB
```

It also lists:

```text
bottom = 0
top = AB
meet = intersection table
join = union table
```

The checker treats the relation and operation tables as untrusted data.

## Replay The Partial Order

The validator checks the finite partial-order laws by enumerating the listed
relation pairs:

```text
reflexive:     x <= x for every element
antisymmetric: x <= y and y <= x implies x = y
transitive:    x <= y and y <= z implies x <= z
bottom:        0 <= x for every x
top:           x <= AB for every x
```

For example:

```text
0 <= A and A <= AB, so 0 <= AB
A <= AB, but AB <= A is not listed
```

The row is accepted only because the finite relation satisfies all of these
checks.

## Replay Meet And Join

The meet and join rows are stronger than just checking table shape. For every
pair, the validator recomputes lower and upper bounds from the order relation.

For example:

```text
lower_bounds(A, B) = {0}
meet(A, B) = 0

upper_bounds(A, B) = {AB}
join(A, B) = AB
```

For `A` and `AB`:

```text
lower_bounds(A, AB) = {0, A}
meet(A, AB) = A

upper_bounds(A, AB) = {AB}
join(A, AB) = AB
```

The listed operation tables pass because every meet is the unique greatest
lower bound and every join is the unique least upper bound.

## Replay Distributivity

The pack checks both finite distributive laws over all triples:

```text
x meet (y join z) = (x meet y) join (x meet z)
x join (y meet z) = (x join y) meet (x join z)
```

One concrete row:

```text
A meet (B join AB) = A meet AB = A
(A meet B) join (A meet AB) = 0 join A = A
```

The validator repeats this for every `x`, `y`, and `z` in `{0,A,B,AB}`.

## Replay Monotone Fixed Points

The second witness is the map:

```text
f(x) = x join A

0  -> A
A  -> A
B  -> AB
AB -> AB
```

The checker verifies monotonicity over every comparable pair:

```text
x <= y implies f(x) <= f(y)
```

It then recomputes the fixed points:

```text
f(A) = A
f(AB) = AB
```

and verifies that `A` is the least fixed point because `A <= AB`.

## Check The Refutation

The bad row uses two distinct elements with both directions listed:

```text
x <= x
y <= y
x <= y
y <= x
```

This relation is reflexive and transitive, but it is not antisymmetric:

```text
x <= y and y <= x, but x != y
```

So the fixed claim that this relation is a partial order is checked `unsat` by
finite replay. The separate `qf-uf-bad-partial-order-antisymmetry` row links the
`QF_UF` artifact that records the two relation-table facts, fixes the
antisymmetry consequence `x = y`, and refutes it against `x != y`; Axeyum emits
and independently rechecks an `UnsatAletheProof` for that equality conflict.

## Check The Set-Family CNF Refutation

The Boolean lattice also has a tiny false top-element row. The actual top is
`AB`, not `A`:

```text
B <= AB
B !<= A
```

A bad claim that `A` is top would require every element to be below `A`,
including:

```text
B <= A
```

The CNF artifact uses one variable:

```text
B_le_A
```

Exact relation replay contributes `not B_le_A`; the false top claim contributes
`B_le_A`. Axeyum emits a DRAT proof, elaborates it to LRAT, and checks both
proof objects. This proves only the fixed finite contradiction, not a theorem
about all lattices.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-order-lattices-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for finite order theory:

```text
untrusted fast search -> candidate relation, meet/join tables, monotone map
trusted small checking -> order laws, bounds, distributivity, fixed points, counterexample row
checked proof object -> QF_UF/Alethe certificate for the explicit antisymmetry row,
                        CNF/DRAT/LRAT certificate for the bad top row
```

Complete lattice theory, Knaster-Tarski fixed-point theorems, Galois
connections, domain theory, Boolean representation theorems, and infinite
order-theoretic facts require stronger proof routes or Lean/mathlib-scale proof
support.
