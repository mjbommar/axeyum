# End To End: Finite Sets

This lesson follows one finite set resource from explicit universes and subsets
to replayed result and proof/evidence status. It uses the
[finite-sets-v0](../../../artifacts/examples/math/finite-sets-v0/) pack.

Concept rows:

- `curriculum_sets` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_set_theory_and_foundations` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `union-intersection-identity` | `sat` | replay-only |
| `subset-transitivity-witness` | `sat` | replay-only |
| `distributive-law-counterexample-rejected` | `unsat` | checked |

The rows are fixed finite set replays. The pack does not claim ZFC set theory,
power-set axioms, ordinals, cardinals, choice principles, or infinite-set
theorems. The malformed distributive-law row also has a concrete CNF/DRAT/LRAT
proof route for the element where equality fails.

## Encode

Each witness fixes a finite universe and named subsets:

```text
universe = {a,b,c,d}
A = {a,b}
B = {b,c}
C = {c,d}
```

The validator first checks that every listed subset element belongs to the
universe. Then it recomputes set operations directly from the element labels.

The intended Axeyum graduation route is a characteristic-vector encoding:

```text
element i in A  <=>  bit i of a is 1
A union B       <=>  a | b
A intersect B  <=>  a & b
A subset B      <=>  (a & ~b) == 0
```

This pack stays one level above that encoding and replays the finite
mathematical data directly.

## Replay Union And Intersection

The first row checks:

```text
A union (B intersect C) = (A union B) intersect (A union C)
```

With:

```text
A = {a,b}
B = {b,c}
C = {c,d}
```

the checker recomputes:

```text
B intersect C = {c}
A union (B intersect C) = {a,b,c}

A union B = {a,b,c}
A union C = {a,b,c,d}
(A union B) intersect (A union C) = {a,b,c}
```

Both sides match, so the fixed row is accepted.

## Replay Subset Transitivity

The second row uses nested finite sets:

```text
A = {0}
B = {0,1}
C = {0,1,2}
```

The checker verifies both premises:

```text
A subset B
B subset C
```

and then replays the conclusion:

```text
A subset C
```

This is a fixed finite witness for subset transitivity, not a universal proof
schema over all sets.

## Replay The Rejected Identity

The bad row checks the malformed identity:

```text
A intersect (B union C) = (A intersect B) union C
```

with:

```text
A = {a}
B = {b}
C = {a,c}
```

The checker recomputes:

```text
B union C = {a,b,c}
A intersect (B union C) = {a}

A intersect B = {}
(A intersect B) union C = {a,c}
```

Since `{a} != {a,c}`, the fixed equality claim is rejected. The evidence is
checked two ways: the validator recomputes the counterexample, and the CNF proof
route checks the element `c` obstruction.

The CNF route introduces Boolean facts for whether `c` is in `A`, `B`, `C`, the
left side, and the right side. The fixed facts force:

```text
left_c = false
right_c = true
```

while the malformed equality requires `left_c = right_c`. The DIMACS artifact
[`distributive-law-counterexample.cnf`](../../../artifacts/examples/math/finite-sets-v0/cnf/distributive-law-counterexample.cnf)
is unsatisfiable; the proof-producing SAT core emits DRAT, and the trusted path
independently checks DRAT and the elaborated LRAT proof.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-sets-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes finite_sets_distributive_counterexample_emits_checked_drat_and_lrat
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for the finite-set base layer:

```text
untrusted fast search -> candidate finite universe and subset data
trusted small checking -> membership, union, intersection, subset, counterexample replay, DRAT/LRAT checks
```

Universal finite-domain identities should graduate to Bool/BV formulas plus
checked SAT/CNF evidence. Infinite set theory, ordinals, cardinals, and choice
principles require stronger proof routes or Lean/mathlib-scale proof support.
