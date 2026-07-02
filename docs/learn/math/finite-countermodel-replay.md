# Finite Countermodel Replay

This page groups the finite counterexample rows that appear across logic,
predicate logic, proof methods, relations/functions, and finite order theory.
It is a bridge lesson for the concept row
`bridge_finite_countermodel_replay`.

The point is small and reusable:

```text
untrusted fast search -> candidate finite object that breaks a claim
trusted small checking -> replay the object against the original finite claim
```

## What Counts As A Finite Countermodel

A finite countermodel is not just a label saying "false." It is a concrete
object with enough data for a checker to recompute the failure:

| Source Shape | Countermodel Data | Checked Failure |
|---|---|---|
| Boolean formula | assignment for every variable | formula evaluates opposite to the alleged theorem |
| finite predicate claim | finite universe plus predicate table | existential, universal, or implication expansion fails |
| relation property | finite relation table | symmetry, antisymmetry, transitivity, or order law fails |
| function claim | finite graph/table | totality, single-valuedness, inverse, or composition claim fails |
| finite lattice/order claim | finite order and meet/join tables | proposed top, order, meet, join, or monotonicity fact fails |

The resource is bounded. A countermodel over a listed universe refutes the
listed finite claim. It does not automatically settle arbitrary first-order
validity, induction schemas, infinite cardinality, or theorem-scale algebra.

## Packs That Reuse The Pattern

| Pack | Rows To Read First | Trust Route |
|---|---|---|
| [`logic-basics-v0`](../../../artifacts/examples/math/logic-basics-v0/) | `and-formula-sat-witness`, `demorgan-equivalence-no-counterexample` | Boolean assignment replay or full truth-table enumeration |
| [`finite-predicate-v0`](../../../artifacts/examples/math/finite-predicate-v0/) | `exists-not-forall-counterexample`, `binary-relation-symmetry-counterexample` | finite universe and predicate/relation table replay |
| [`proof-methods-patterns-v0`](../../../artifacts/examples/math/proof-methods-patterns-v0/) | `invalid-converse-counterexample`, `proof-by-cases-no-counterexample` | Boolean assignment replay or truth-table enumeration |
| [`relations-functions-v0`](../../../artifacts/examples/math/relations-functions-v0/) | `non-function-rejected`, `qf-uf-function-single-valued-alethe` | finite function-table replay plus QF_UF/Alethe for the equality conflict |
| [`finite-order-lattices-v0`](../../../artifacts/examples/math/finite-order-lattices-v0/) | `bad-partial-order-rejected`, `bad-top-element-rejected` | finite relation/table replay plus checked QF_UF or Bool/CNF evidence |

## Replay A Boolean Countermodel

For a proposed implication, the checker only needs the variables and one
assignment:

```text
claim:       p -> q implies q -> p
assignment:  p = false, q = true
```

The replay is direct:

```text
p -> q = true
q -> p = false
```

The assignment is a countermodel to the converse inference. It is not a proof
about every proof calculus; it is a finite Boolean refutation of this encoded
claim.

## Replay A Predicate Countermodel

For a finite predicate row, the countermodel must name the universe and every
predicate value the quantifier expansion will read:

```text
U = {a,b}
P(a) = true
P(b) = false
```

The checker expands the finite quantifiers:

```text
exists x. P(x) = P(a) or P(b) = true
forall x. P(x) = P(a) and P(b) = false
```

So this table witnesses `exists x. P(x)` while refuting `forall x. P(x)`.

## Replay A Relation Or Function Countermodel

For a relation property, the checker replays table membership:

```text
R(a,b) = true
R(b,a) = false
```

Symmetry would require `R(a,b) -> R(b,a)`, so the listed table is enough to
reject the symmetry claim.

For a function claim, the checker validates the graph shape before trusting the
row. A graph that maps one input to two outputs is not a function:

```text
f(x0) = y0
f(x0) = y1
y0 != y1
```

The replay route checks the duplicate input. The QF_UF/Alethe route can then
isolate the equality conflict behind the same mathematical failure.

## Replay A Finite Order Countermodel

For an order or lattice row, the countermodel is a finite relation/table
failure. The false top-element row in the Boolean lattice says `A` is top, but
the replay table contains:

```text
B !<= A
```

A top element must have every element below it. The checker only needs the
finite order table to reject the bad claim, and a small Bool/CNF proof route
can separately certify the isolated impossible condition.

## Query It

From the repository root:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --text countermodel \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_countermodel_replay \
  --proof-status checked \
  --require-any
```

Validate the source packs:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-predicate-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-patterns-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/relations-functions-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-order-lattices-v0
```

## Boundary

Finite countermodels are strong evidence for the finite statement they replay.
They are deliberately not advertised as full first-order validity, induction,
compactness, completeness, or infinite-structure theorems. Those remain
Lean-horizon or theorem-reconstruction work until a kernel-checked proof route
exists.
