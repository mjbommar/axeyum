# Cardinality Theorem Boundary

This page separates Axeyum's finite cardinality resources from infinite
cardinality theorems, countability/uncountability, choice principles,
Schroeder-Bernstein, and cardinal arithmetic.

Primary packs:

- [finite-cardinality-v0](../../../artifacts/examples/math/finite-cardinality-v0/)
- [cardinality-principles-v0](../../../artifacts/examples/math/cardinality-principles-v0/)

Companion lessons and maps:

- [End To End: Finite Cardinality](finite-cardinality-end-to-end.md)
- [End To End: Cardinality Principles](cardinality-principles-end-to-end.md)
- [Sets, Relations, And Finite Structures](sets-relations-and-finite-structures.md)
- [Foundations And Discrete Resource Consumer Queries](../../foundational-resources/FOUNDATIONS-DISCRETE-QUERIES.md)
- [Theorem Horizon Queries](../../foundational-resources/THEOREM-HORIZON-QUERIES.md)

## Current Finite Resources

`finite-cardinality-v0` checks finite function graphs. The validator does not
trust labels like "bijection" or "injection." It recomputes totality,
single-valuedness, injectivity, surjectivity, and finite function-space
enumeration from the listed data.

`cardinality-principles-v0` checks finite set and incidence tables. It
recomputes unions, intersections, subset tables, powersets, degree sums, and
integer counts before accepting a cardinality row.

The checked resources cover:

```text
finite bijection witness:          3 -> 3 explicit graph       -> checked finite replay
proper-subset injection witness:   2 -> 3 explicit graph       -> checked finite replay
no injection 4 -> 3:               81 functions enumerated     -> checked Bool/CNF evidence
no surjection 2 -> 3:              9 functions enumerated      -> checked finite replay
inclusion-exclusion:               overlapping finite sets     -> checked finite replay
disjoint union additivity:         side condition replay       -> checked finite replay
double counting:                   bipartite incidence table   -> checked finite replay
powerset cardinality:              listed P({p,q,r})           -> checked finite replay
bad overlap additivity:            4 = 6 contradiction         -> checked QF_LIA/Diophantine
Cantor / Schroeder-Bernstein:      arbitrary infinite sets     -> Lean/theorem work
```

The promoted negative rows pin source artifacts:

```text
no-injection-four-to-three.cnf
overlap-additivity-diophantine-conflict.smt2
```

Those prove bounded finite refutations and extracted integer contradictions.
They do not prove any theorem about arbitrary finite sizes unless that theorem
is explicitly encoded, and they do not prove infinite cardinality statements.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `finite-bijection-cardinality-witness` | `sat` | checked finite replay | A displayed three-to-three function graph is a bijection. |
| `proper-subset-injection-witness` | `sat` | checked finite replay | A displayed two-to-three graph is injective and not surjective. |
| `no-injection-four-to-three` | `unsat` | checked Bool/CNF evidence | There is no injective function from this fixed four-element set to this fixed three-element set. |
| `no-surjection-two-to-three` | `unsat` | checked finite replay | There is no surjective function from this fixed two-element set to this fixed three-element set. |
| `inclusion-exclusion-two-sets` | `sat` | checked finite replay | The listed finite sets satisfy two-set inclusion-exclusion. |
| `disjoint-union-additivity` | `sat` | checked finite replay | The listed finite sets satisfy additivity because disjointness is checked. |
| `double-counting-bipartite-edges` | `sat` | checked finite replay | Both degree sums count the same fixed edge table. |
| `finite-powerset-cardinality` | `sat` | checked finite replay | The listed powerset of a three-element set has eight members. |
| `overlapping-disjoint-additivity-counterexample` | `sat` | checked finite replay | The listed overlap is a counterexample to the false unrestricted additivity rule. |
| `overlap-additivity-count-conflict` | `unsat` | checked QF_LIA/Diophantine | The replayed counts make the malformed equality `4 = 6` impossible. |
| `cantor-diagonal-lean-horizon` | `not-run` | Lean horizon | No-surjection from `N` onto `P(N)` remains future proof work. |
| `cantor-schroeder-bernstein-lean-horizon` | `not-run` | Lean horizon | Cantor-Schroeder-Bernstein for arbitrary sets remains future proof work. |

The boundary is:

```text
untrusted fast search -> finite function graph, finite set table, count claim
trusted small checking -> replayed totality/counts plus checked finite refutations
theorem horizon       -> Cantor, Schroeder-Bernstein, countability, choice, cardinal arithmetic
```

## What Is Not Proved Yet

The current packs do not prove:

- Cantor diagonalization for arbitrary sets beyond the named horizon row;
- Cantor-Schroeder-Bernstein for arbitrary sets;
- countability or uncountability of standard sets;
- cardinal arithmetic laws for infinite cardinals;
- choice principles, well-ordering, ordinals, cofinality, or ZFC metatheory;
- general pigeonhole/injection/surjection schemas parameterized by all finite
  sizes, unless a future proof resource encodes those schemas explicitly.

Those claims need theorem statements, set-theoretic hypotheses, and no-`sorry`
proof artifacts before they can graduate from horizon metadata to theorem
coverage.

## Query The Boundary

Find checked finite cardinality rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-cardinality-v0 \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack cardinality-principles-v0 \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_bijection_cardinality \
  --proof-status checked \
  --require-any
```

Find the checked proof routes that go beyond plain replay:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-cardinality-v0 \
  --route boolean \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack cardinality-principles-v0 \
  --route Diophantine \
  --proof-status checked \
  --require-any
```

Find the explicit infinite-cardinality theorem horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text Cantor \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-cardinality-v0 \
  --expected-result not-run \
  --proof-status lean-horizon \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack cardinality-principles-v0 \
  --expected-result not-run \
  --proof-status lean-horizon \
  --require-any
```

Drill into individual teaching rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-cardinality-v0 \
  --text injection \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack cardinality-principles-v0 \
  --text powerset \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack cardinality-principles-v0 \
  --text overlap \
  --proof-status checked \
  --require-any
```

## Graduation Criteria

Cardinality resources graduate only when they add:

1. precise theorem statements for Cantor diagonalization,
   Cantor-Schroeder-Bernstein, countability, or infinite cardinal arithmetic;
2. explicit set-theoretic assumptions, including any use of choice or
   well-ordering;
3. no-`sorry` proof artifacts for each theorem claim before display labels
   change from finite replay to theorem coverage;
4. a kernel-checked route that connects finite examples to the theorem
   statement only where such a connection is actually proved;
5. display labels that keep finite function replay, finite count replay,
   Boolean/CNF evidence, QF_LIA/Diophantine evidence, and infinite theorem
   horizons separate.

Until then, the cardinality packs remain finite checked resources and compact
bridges to future set-theory proof resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cardinality-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/cardinality-principles-v0
python3 scripts/query-foundational-resources.py checks --pack finite-cardinality-v0 --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack cardinality-principles-v0 --proof-status checked --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --text Cantor --require-any
```

Expected resource boundary: the finite cardinality rows validate, the checked
negative rows stay finite or extracted-arithmetic evidence, and Cantor-style
infinite cardinality remains an explicit Lean/theorem horizon.
