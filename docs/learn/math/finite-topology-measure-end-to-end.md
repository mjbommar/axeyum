# End To End: Finite Topology And Measure

This lesson follows two exact finite set-family resources from topology axiom
replay to closure/interior, metric balls, finite sigma-algebras, exact finite
measure additivity, and event complements. It uses
[finite-topology-v0](../../../artifacts/examples/math/finite-topology-v0/)
and [finite-measure-v0](../../../artifacts/examples/math/finite-measure-v0/).

Concept rows:

- `curriculum_sets`, `curriculum_reals`, `curriculum_rationals`,
  `curriculum_counting`, and `curriculum_sequences_and_limits` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_topology`, `field_measure_theory`,
  `field_set_theory_and_foundations`, `field_real_analysis`, and
  `field_probability_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `finite-topology-axioms` | `sat` | replay-only |
| `closure-interior-witness` | `sat` | replay-only |
| `metric-ball-witness` | `sat` | replay-only |
| `finite-sigma-algebra-axioms` | `sat` | replay-only |
| `finite-measure-additivity` | `sat` | replay-only |
| `event-complement-measure` | `sat` | replay-only |

Every row is finite replay over explicit sets and exact rational values. These
packs do not claim compactness, connectedness, continuity, countable additivity,
Lebesgue measure, or convergence theorems.

## Replay A Finite Topology

The topology witness uses:

```text
universe = {a,b,c}
open sets = {}, {a}, {a,b}, {a,b,c}
```

The validator checks:

```text
{} is open
{a,b,c} is open
pairwise unions of listed opens are listed opens
pairwise intersections of listed opens are listed opens
```

Because the universe is finite, this is direct set-family replay.

## Replay Closure And Interior

For the subset:

```text
S = {b}
```

the witness records:

```text
interior(S) = {}
closure(S) = {b,c}
```

The validator recomputes the interior as the largest listed open subset of
`S`. It recomputes closure by complementing the interior of the complement:

```text
complement(S) = {a,c}
interior(complement(S)) = {a}
closure(S) = complement({a}) = {b,c}
```

## Replay A Finite Metric Ball

The finite metric-space row uses points:

```text
p0, p1, p2
```

with exact distances:

```text
d(p0,p1) = 1
d(p1,p2) = 2
d(p0,p2) = 3
```

The open ball has:

```text
center = p1
radius = 3/2
```

The validator includes points with distance strictly below `3/2`:

```text
d(p1,p1) = 0
d(p1,p0) = 1
d(p1,p2) = 2
ball(p1, 3/2) = {p0,p1}
```

This is exact rational comparison over a finite metric table.

## Replay A Finite Sigma-Algebra

The measure pack uses a four-point universe:

```text
universe = {a,b,c,d}
measurable sets = {}, {a,b}, {c,d}, {a,b,c,d}
```

The validator checks:

```text
{} and universe are measurable
complements of measurable sets are measurable
pairwise unions of measurable sets are measurable
```

This is finite sigma-algebra replay, not countable-additivity proof.

## Replay A Finite Measure

The probability measure is:

```text
mu({}) = 0
mu({a,b}) = 1/3
mu({c,d}) = 2/3
mu({a,b,c,d}) = 1
```

The validator checks nonnegativity, normalization, and finite additivity on
disjoint measurable sets:

```text
{a,b} disjoint {c,d}
mu({a,b}) + mu({c,d}) = 1/3 + 2/3 = 1
mu({a,b,c,d}) = 1
```

## Replay Event Complements

For the event:

```text
E = {a,b}
```

the complement is:

```text
E^c = {c,d}
```

The validator checks:

```text
mu(E) = 1/3
mu(E^c) = 2/3
mu(E) + mu(E^c) = 1
```

This is the finite probability shadow that later supports integration,
conditional expectation, and stochastic-kernel packs.

## Name The Lean Horizon

The packs do not claim broad topology or measure theory:

```text
arbitrary topological spaces
compactness and connectedness theorems
continuity theorems
countable additivity
Lebesgue measure
convergence theorems
```

Those require Lean-backed topology/measure resources or a stronger proof route.
These packs only check finite set-family and exact rational measure tables.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-measure-v0
```

Expected output for each command:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current finite topology/measure resource pattern:

```text
untrusted fast search -> set family, metric ball, measure, or complement row
trusted small checking -> finite set operations and exact rational arithmetic
remaining horizon -> infinite topology, countable measure, and convergence
```

The graduation route is deterministic finite replay plus checked proof objects
for false set-family or measure-table claims before general topological or
measure-theoretic theorems are promoted.
