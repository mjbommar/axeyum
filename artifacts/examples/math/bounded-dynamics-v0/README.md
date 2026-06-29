# Bounded Dynamics V0

This pack covers tiny exact-rational recurrence and finite transition-system
examples for the `differential_equations_and_dynamical_systems` field-extension
row. It is the discrete, bounded shadow of dynamical systems: fixed horizons,
explicit initial states, and replayed traces.

The examples are intentionally small:

- a linear recurrence trace;
- a bounded invariant witness over that trace;
- a reachable threshold witness over a finite horizon.

## Concepts

- `field_differential_equations_and_dynamical_systems`
- `field_numerical_analysis`
- `field_linear_algebra`
- `curriculum_calculus`
- `curriculum_linear_algebra`
- `curriculum_sequences_and_limits`

## Trust Story

The current validator parses all states and coefficients as exact rational
strings. It checks that each trace starts at the claimed initial state, follows
the listed affine update `x(t+1) = x(t) + delta`, and satisfies the claimed
bounded invariant or threshold reachability condition.

This pack does not yet emit SMT-LIB or call Axeyum's bounded-model-checking
route. Continuous-time dynamics, ODE existence and uniqueness, stability, chaos,
and PDE theory remain proof-horizon material.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-dynamics-v0
```
