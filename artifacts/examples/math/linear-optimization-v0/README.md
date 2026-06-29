# Linear Optimization V0

This pack covers small exact-rational linear-optimization examples for the
`optimization_and_convexity` field-extension row. It uses fixed-dimensional LP
constraints and exact replay, not floating-point solvers.

The examples are the optimization shadow that will later map to Axeyum's
QF_LRA route:

- feasible point replay for a two-variable linear system;
- feasible objective-threshold witness;
- infeasible objective-threshold check with a tiny Farkas certificate.

## Concepts

- `field_optimization_and_convexity`
- `field_linear_algebra`
- `field_real_analysis`
- `curriculum_linear_algebra`
- `curriculum_rationals`
- `curriculum_reals`

## Trust Story

The current validator parses all coefficients, bounds, and witnesses exactly as
rational strings. It checks feasibility by replaying linear inequalities and
checks the infeasible threshold by verifying that nonnegative Farkas
multipliers cancel all variables and derive an impossible constant inequality.
The infeasible-threshold row also has an Axeyum regression that builds the
corresponding `QF_LRA` inequalities, emits `UnsatFarkas` evidence, and rechecks
that evidence independently. The feasible witness rows remain exact replay-only
until they route through model evidence.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-optimization-v0
cargo test -p axeyum-solver --test math_resource_lra_routes linear_optimization_objective_threshold_emits_checked_farkas
```
