# Finite Measure Monotonicity V0

This pack extends the `measure_theory` curriculum lane with finite
monotonicity and subadditivity checks. It treats a finite probability space as
a normalized exact-rational measure table: candidate events and claims are
untrusted, and every subset relation, union, intersection, difference, and
measure identity is replayed before solver evidence is trusted.

The pack covers:

- finite powerset sigma-algebra and normalized measure-table replay;
- subset monotonicity via `B = A disjoint-union (B \ A)`;
- finite union subadditivity via inclusion-exclusion;
- checked QF_LRA/Farkas rejection of malformed subset-measure and
  union-subadditivity claims;
- a Lean-horizon row for monotone convergence, countable subadditivity, and
  general measure-space reasoning.

## Concepts

- `field_measure_theory`
- `field_probability_theory`
- `field_set_theory_and_foundations`
- `curriculum_sets`
- `curriculum_rationals`
- `curriculum_counting`
- `bridge_finite_measure_additivity`

## Trust Story

The validator parses all measures as exact rational strings, checks the
powerset sigma-algebra, validates finite additivity, and then recomputes each
event measure from the table. Monotonicity and subadditivity are accepted only
after the finite set identities and exact rational inequalities replay.

The promoted bad rows keep the measure-theory computation outside the solver.
Finite replay computes `mu({a}) = 1/6`, `mu(A union B) = 1`, and
`mu(A)+mu(B)=4/3`; the source SMT-LIB artifacts check only the final equality
or inequality conflicts against the false claims through Axeyum's
`UnsatFarkas` evidence path.

This pack does not claim countable additivity, monotone convergence, dominated
convergence, or almost-everywhere reasoning.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-measure-monotonicity-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_measure_monotonicity_bad_subset_measure_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_measure_monotonicity_bad_union_subadditivity_artifact_emits_checked_farkas
```
