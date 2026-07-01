# Finite Concentration V0

This pack adds exact finite concentration checks. It treats Markov's
inequality, Chebyshev's inequality, and the union bound as finite rational
table replays over explicitly listed probability atoms.

The examples are:

- a Markov inequality witness for a nonnegative finite random variable;
- a Chebyshev inequality witness for a finite centered variable;
- a union-bound witness for two finite events;
- checked rejection of false concentration and union bounds;
- a concentration/limit-theorem Lean-horizon row.

## Concepts

- `field_probability_theory`
- `field_statistics`
- `field_measure_theory`
- `field_real_analysis`
- `field_set_theory_and_foundations`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_rationals`
- `curriculum_counting`

## Trust Story

The validator checks normalized atom probabilities, recomputes finite
expectations, variances, tail events, event unions, and each listed bound using
exact rational arithmetic. The bad-bound rows are checked by recomputing the
actual tail and union probabilities and confirming each exceeds the claimed
bound. Those rows also have Axeyum regressions that take the replayed
probability, build the false `QF_LRA` bound claim, emit `UnsatFarkas`
evidence, and recheck that evidence independently.

This pack is finite checked evidence. It is not a proof of general
concentration theory, laws of large numbers, central limit theorems,
martingale inequalities, or asymptotic statistics.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-concentration-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_concentration_bad_tail_bound_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_concentration_bad_union_bound_artifact_emits_checked_farkas
```
