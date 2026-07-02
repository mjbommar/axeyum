# Finite Martingales V0

This pack adds exact finite martingale checks. It treats a filtration as a
time-indexed sequence of finite partitions of probability atoms and checks
adaptedness, martingale conditional-expectation equalities, a square
submartingale witness, and a bounded stopping-time replay.

The examples are:

- a finite martingale witness for a two-step fair walk;
- a square-submartingale witness;
- a bounded optional-stopping replay row;
- replay rejection of false stopped-expectation and martingale claims;
- separate checked QF_LRA/Farkas rows for the isolated linear conflicts;
- a general martingale and stopping-theorem Lean-horizon row.

## Concepts

- `field_probability_theory`
- `field_measure_theory`
- `field_statistics`
- `field_real_analysis`
- `field_set_theory_and_foundations`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_rationals`
- `curriculum_counting`

## Trust Story

The validator checks normalized finite atom probabilities, verifies that each
filtration level is a partition, checks that process values are constant on
the corresponding information blocks, recomputes
`E[M_{t+1} | F_t] = M_t`, checks a finite square-submartingale inequality,
and replays a bounded stopping time by exact rational expectation.

The malformed stopped-expectation and martingale replay rows stay replay-only:
they recompute the stopped expectation and conditional expectation from the
finite tables. Separate `qf-lra-*` rows point at source-linked QF_LRA/Farkas
regressions for the isolated exact-linear contradictions. This pack is not a
proof of general martingale convergence, optional stopping, Doob inequalities,
or stochastic integration.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-martingales-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_martingales_bad_stopped_expectation_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_martingales_bad_conditional_expectation_emits_checked_farkas
```
