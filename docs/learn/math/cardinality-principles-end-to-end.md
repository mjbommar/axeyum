# End To End: Cardinality Principles

This lesson follows one finite cardinality-principles resource from set and
incidence tables to replayed result and proof/evidence status. It uses the
[cardinality-principles-v0](../../../artifacts/examples/math/cardinality-principles-v0/)
pack.

Concept rows:

- `curriculum_cardinality`, `curriculum_sets`,
  `curriculum_relations_and_functions`, and `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_set_theory_and_foundations` and `field_discrete_math` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `inclusion-exclusion-two-sets` | `sat` | checked |
| `disjoint-union-additivity` | `sat` | checked |
| `double-counting-bipartite-edges` | `sat` | checked |
| `finite-powerset-cardinality` | `sat` | checked |
| `overlapping-disjoint-additivity-counterexample` | `sat` | checked |
| `overlap-additivity-count-conflict` | `unsat` | checked QF_LIA/Diophantine |
| `cantor-schroeder-bernstein-lean-horizon` | `not-run` | lean-horizon |

The checked rows are finite set, subset, and incidence-table replay rows. The
pack does not claim arbitrary cardinal arithmetic, Cantor-Schroeder-Bernstein,
countability, uncountability, or choice principles.

## Encode

The pack models cardinality principles as finite data:

```text
sets:       explicit element lists
relations:  explicit incidence pairs
counts:     integers replayed from those lists and pairs
```

The checker does not trust a producer's claimed count. It recomputes the
finite union, intersection, subset table, or degree table from the listed data.

## Replay Inclusion-Exclusion

The overlapping two-set witness is:

```text
A = {a,b,c}
B = {b,c,d}
A union B = {a,b,c,d}
A intersect B = {b,c}
```

The checker recomputes the listed sets and counts:

```text
|A| = 3
|B| = 3
|A union B| = 4
|A intersect B| = 2
```

It then replays the two-set inclusion-exclusion equation:

```text
4 = 3 + 3 - 2
```

## Replay Disjoint-Union Additivity

The disjoint-union witness is:

```text
left  = {x0,x1}
right = {y0,y1,y2}
union = {x0,x1,y0,y1,y2}
```

Before accepting the additive count, the validator checks disjointness:

```text
left intersect right = {}
```

Then it replays:

```text
|left union right| = 5 = 2 + 3
```

This explains the side condition that the false counterexample row will break:
plain additivity needs disjointness.

## Replay Double Counting

The double-counting witness is a finite bipartite edge table:

```text
edges = {
  (u0,v0), (u0,v1), (u1,v0), (u2,v1)
}
```

The checker recomputes left degrees:

```text
deg(u0) = 2
deg(u1) = 1
deg(u2) = 1
sum = 4
```

and right degrees:

```text
deg(v0) = 2
deg(v1) = 2
sum = 4
```

Both degree sums count the same four edge rows.

## Replay Powerset Cardinality

The powerset witness lists every subset of `{p,q,r}`:

```text
{}
{p}, {q}, {r}
{p,q}, {p,r}, {q,r}
{p,q,r}
```

The validator enumerates the powerset independently and compares the table
entry-for-entry as a set of subsets. There are eight listed subsets, so the row
replays:

```text
|P({p,q,r})| = 8 = 2^3
```

## Check The False-Rule Counterexample

The counterexample row reuses the overlapping sets:

```text
A = {a,b,c}
B = {b,c,d}
```

The false rule says:

```text
|A union B| = |A| + |B|
```

But the validator recomputes:

```text
|A union B| = 4
|A| + |B| = 6
```

The expected result is `sat` because the row is a checked counterexample to the
false universal rule, not a proof that the false rule is valid.

The promoted solver row then turns the replayed counts into a tiny integer
contradiction:

```text
union_count = 4
claimed_disjoint_sum = 6
union_count = claimed_disjoint_sum
```

That source artifact lives at
`artifacts/examples/math/cardinality-principles-v0/smt2/overlap-additivity-diophantine-conflict.smt2`.
The route emits and checks `UnsatDiophantine` evidence for the impossible
equality.

## Name The Infinite Horizon

The final row records the theorem-prover boundary:

```text
Cantor-Schroeder-Bernstein for arbitrary sets
```

The finite rows teach executable counting shapes. They do not replace a
kernel-checked proof for arbitrary infinite-cardinality theorems.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/cardinality-principles-v0
cargo test -p axeyum-solver --test math_resource_lia_routes cardinality_principles_overlap_additivity_emits_checked_diophantine_evidence
```

The validator prints:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for finite counting principles:

```text
untrusted fast search -> candidate set tables, incidence table, subset list
trusted small checking -> recomputed counts, side conditions, QF_LIA certificate
```

General cardinal arithmetic, countability, uncountability,
Cantor-Schroeder-Bernstein, and choice principles require stronger proof routes
or Lean/mathlib-scale proof support.
