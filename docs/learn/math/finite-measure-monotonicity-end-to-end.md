# End To End: Finite Measure Monotonicity

This lesson follows one finite measure resource from a normalized powerset
measure table to subset monotonicity, union subadditivity, and checked
rejection of malformed subset-measure and union-subadditivity rows. It uses the
[finite-measure-monotonicity-v0](../../../artifacts/examples/math/finite-measure-monotonicity-v0/)
pack.

Concept rows:

- `field_measure_theory`, `field_probability_theory`, and
  `field_set_theory_and_foundations` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_sets`, `curriculum_rationals`, and `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `bridge_finite_measure_additivity` and `family_exact_rational_farkas` in the
  atlas bridge/example-family vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `finite-measure-table` | `sat` | replay-only |
| `subset-monotonicity-witness` | `sat` | replay-only |
| `finite-union-subadditivity-witness` | `sat` | replay-only |
| `bad-subset-measure-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-union-subadditivity-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-measure-monotonicity-lean-horizon` | `not-run` | Lean horizon |

All finite rows are exact rational table checks. The pack does not prove
countable additivity, monotone convergence, dominated convergence, or
almost-everywhere facts.

## Encode

The finite measure lives on the full powerset of:

```text
U = {a,b,c}
```

The atom masses are:

```text
mu({a}) = 1/6
mu({b}) = 1/3
mu({c}) = 1/2
```

The table lists every subset, so set operations become finite replay:

```text
{a} subset {a,b}
{a,b} \ {a} = {b}
{a,b} union {b,c} = {a,b,c}
{a,b} intersect {b,c} = {b}
```

## Replay

For monotonicity, the checker recomputes:

```text
mu({a,b}) = mu({a}) + mu({b})
1/2 = 1/6 + 1/3
mu({a}) <= mu({a,b})
```

For subadditivity, it checks inclusion-exclusion:

```text
mu({a,b,c}) = mu({a,b}) + mu({b,c}) - mu({b})
1 = 1/2 + 5/6 - 1/3
mu({a,b,c}) <= mu({a,b}) + mu({b,c})
```

## Check The Refutation

The promoted bad row keeps the source table fixed but changes the subset
measure claim:

```text
computed mu({a}) = 1/6
claimed mu({a}) = 2/3
```

The committed SMT-LIB artifact
[`bad-subset-measure-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-measure-monotonicity-v0/smt2/bad-subset-measure-farkas-conflict.smt2)
checks only the final exact-rational contradiction.

The second promoted bad row keeps the source table fixed but changes the union
measure claim:

```text
computed mu(A union B) = 1
computed mu(A) + mu(B) = 4/3
claimed mu(A union B) = 3/2
```

The committed SMT-LIB artifact
[`bad-union-subadditivity-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-measure-monotonicity-v0/smt2/bad-union-subadditivity-farkas-conflict.smt2)
checks only the final exact-linear inequality contradiction.

The solver search is untrusted. The accepted evidence is rechecked
`UnsatFarkas` arithmetic over the source artifact.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-measure-monotonicity-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_measure_monotonicity_bad_subset_measure_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_measure_monotonicity_bad_union_subadditivity_artifact_emits_checked_farkas
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate measure table, event relation, or Farkas certificate
trusted small checking -> finite set replay, exact rational arithmetic, checked QF_LRA evidence
remaining horizon -> countable measure, convergence theorems, and almost-everywhere reasoning
```

Use this page after
[End To End: Finite Measure](finite-measure-end-to-end.md) when the goal is to
turn finite additivity into monotonicity and subadditivity obligations.
