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
It does not yet emit SMT-LIB or call Axeyum's LRA/Farkas backend for these pack
instances.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-optimization-v0
```
