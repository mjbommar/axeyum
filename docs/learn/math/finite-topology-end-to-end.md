# End To End: Finite Topology

This lesson follows one finite topology resource from set-family data to
closure/interior replay, exact metric-ball replay, and checked rejection of a
malformed topology row. It uses the
[finite-topology-v0](../../../artifacts/examples/math/finite-topology-v0/)
pack.

Concept rows:

- `field_topology`, `field_set_theory_and_foundations`, and
  `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_sets`, `curriculum_reals`, and
  `curriculum_sequences_and_limits` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `bridge_finite_boolean_algebra`, `bridge_metric_ball`, and
  `bridge_compactness_shadow` in the atlas bridge vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `finite-topology-axioms` | `sat` | replay-only |
| `closure-interior-witness` | `sat` | replay-only |
| `metric-ball-witness` | `sat` | replay-only |
| `bad-empty-open-rejected` | `unsat` | checked Bool/CNF DRAT/LRAT |

All rows are finite. The pack checks explicit open-set families, exact finite
set operations, and exact rational distance comparisons. It does not prove
general compactness, connectedness, continuity, metrization, or arbitrary
topological-space theorems.

## Encode

The topology witness is a three-point space:

```text
universe = {a,b,c}
open sets = {}, {a}, {a,b}, {a,b,c}
```

The validator checks the finite topology axioms directly:

```text
{} is open
{a,b,c} is open
pairwise unions of listed opens are listed opens
pairwise intersections of listed opens are listed opens
```

The closure/interior row uses the same topology and the subset:

```text
S = {b}
interior(S) = {}
closure(S) = {b,c}
```

The metric-ball row is separate exact finite metric data:

```text
points = p0, p1, p2
d(p0,p1) = 1
d(p1,p2) = 2
d(p0,p2) = 3
center = p1
radius = 3/2
ball = {p0,p1}
```

## Replay

For interior, the checker searches only the listed open sets. The open subsets
of `{b}` are:

```text
{}
```

so the largest open subset is `{}`.

For closure, the checker uses complements inside the finite universe:

```text
complement({b}) = {a,c}
interior({a,c}) = {a}
closure({b}) = complement({a}) = {b,c}
```

For the metric ball, the checker compares exact rational distances:

```text
d(p1,p1) = 0 < 3/2
d(p1,p0) = 1 < 3/2
d(p1,p2) = 2 >= 3/2
```

Therefore the ball is exactly `{p0,p1}`.

## Check The Refutation

The promoted bad row uses a two-point open-set table:

```text
universe = {a,b}
open_sets = {a}, {a,b}
```

This table omits `{}` even though every topology must contain the empty set.
The source DIMACS artifact isolates the final Boolean contradiction:

```text
empty_is_open = false
empty_is_open = true
```

The SAT search is untrusted. The accepted evidence is the independent DRAT
check plus elaborated LRAT check over the committed CNF artifact
[`bad-empty-open-rejected.cnf`](../../../artifacts/examples/math/finite-topology-v0/cnf/bad-empty-open-rejected.cnf).

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes finite_topology_bad_empty_open_emits_checked_drat_and_lrat
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate open-set family, metric ball, or proof object
trusted small checking -> finite set replay, rational comparison, checked DRAT/LRAT
remaining horizon -> general topology theorems and infinite-space proof work
```

Use this page for the first-principles finite topology story. For the
cross-field bridge from topology into finite sigma-algebras and measures, read
[End To End: Finite Topology And Measure](finite-topology-measure-end-to-end.md).
