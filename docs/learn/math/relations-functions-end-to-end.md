# End To End: Relations And Functions

This lesson follows one finite relations/functions resource from relation and
graph tables to replayed result and proof/evidence status. It uses the
[relations-functions-v0](../../../artifacts/examples/math/relations-functions-v0/)
pack.

Concept rows:

- `curriculum_relations_and_functions` and `curriculum_sets` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_set_theory_and_foundations` and `field_discrete_math` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `partial-order-witness` | `sat` | replay-only |
| `bijection-table-witness` | `sat` | replay-only |
| `non-function-rejected` | `unsat` | checked |
| `qf-uf-function-single-valued-alethe` | `unsat` | checked |

The first three rows are finite table checks. The final row is a concrete
QF_UF proof-object check for function consistency. The pack does not claim
general function theory, choice principles, quotient constructions, or
infinite-domain cardinality facts.

## Encode

Relations are explicit sets of ordered pairs. For a relation on a finite
carrier `E`, the validator checks:

```text
reflexive:     for every x in E, (x,x) is listed
antisymmetric: if (x,y) and (y,x) are listed, then x = y
transitive:    if (x,y) and (y,z) are listed, then (x,z) is listed
```

Functions are finite graph tables from a declared domain to a declared
codomain:

```text
total:         every domain element has at least one output
single-valued: every domain element has at most one output
injective:     distinct inputs have distinct outputs
surjective:    every codomain element is hit
```

The proof-object row uses the QF_UF route where function consistency and
congruence are checked by EUF evidence. The finite table rows still replay
directly.

## Replay A Partial Order

The first witness is the divisibility relation on `{1,2,4}`:

```text
(1,1), (1,2), (1,4)
(2,2), (2,4)
(4,4)
```

The checker verifies reflexivity:

```text
(1,1), (2,2), and (4,4) are listed
```

It verifies antisymmetry because the only two-way pairs are reflexive pairs.
It verifies transitivity by checking all composable pairs. For example:

```text
(1,2) and (2,4) imply (1,4)
```

So the fixed finite relation is accepted as a partial order.

## Replay A Bijection Table

The bijection witness maps:

```text
x0 -> y1
x1 -> y2
x2 -> y0
```

The checker first verifies this is a function:

```text
each of x0, x1, x2 has exactly one output
```

Then it verifies injectivity and surjectivity:

```text
outputs = {y1, y2, y0}
codomain = {y0, y1, y2}
```

Every codomain element is hit exactly once, so the graph is a bijection.

## Check The Non-Function Refutation

The bad graph lists:

```text
x0 -> y0
x0 -> y1
x1 -> y1
```

The fixed false claim says this graph is a function. The validator rejects it
because `x0` has two distinct outputs:

```text
y0 != y1
```

The result is checked `unsat` for this fixed graph. It is a finite table
refutation, not a theorem about all malformed graphs.

## Check The QF_UF Function Conflict

The proof-object row encodes the same single-valuedness idea as a pure EUF
conflict:

```text
f(x0) = y0
f(x0) = y1
y0 != y1
```

The artifact lives at
`artifacts/examples/math/relations-functions-v0/smt2/function-single-valued-conflict.smt2`.
The resource regression checks that Axeyum emits `Evidence::UnsatAletheProof`
with the pure EUF Alethe emitter and then rechecks the proof independently.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/relations-functions-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for the finite relation/function
base layer:

```text
untrusted fast search -> candidate relation or function graph
trusted small checking -> relation laws, function totality, single-valuedness, bijection replay, Alethe equality proof
```

General function-space theorems, choice-dependent existence principles,
quotient constructions over arbitrary relations, and infinite-domain
cardinality facts require stronger proof routes or Lean/mathlib-scale proof
support.
