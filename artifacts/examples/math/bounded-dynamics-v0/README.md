# Bounded Dynamics V0

This pack covers tiny exact-rational recurrence and finite transition-system
examples for the `differential_equations_and_dynamical_systems` field-extension
row. It is the discrete, bounded shadow of dynamical systems: fixed horizons,
explicit initial states, and replayed traces.

The examples are intentionally small:

- a linear recurrence trace;
- a bounded invariant witness over that trace;
- a reachable threshold witness over a finite horizon;
- a malformed transition-step row whose next state contradicts exact replay
  and is checked through QF_LRA/Farkas evidence;
- a malformed threshold-step row whose early reachability claim contradicts
  exact replay and is checked through QF_LRA/Farkas evidence;
- a malformed invariant-bound row whose final exact state contradicts the
  claimed upper bound and is checked through QF_LRA/Farkas evidence.

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

The checked bad rows emit tiny source-linked QF_LRA artifacts: transition replay
computes `2 + 2 = 4` while a malformed row claims the next state is `5`, and
reachability replay computes state `6` at step `2` while the threshold is `7`,
and invariant replay computes the terminal state `8` while a malformed
invariant claims `x(t) <= 6`. The `math_resource_lra_routes` regressions parse
those artifacts, emit `UnsatFarkas` evidence, and independently recheck the
certificates.
Continuous-time dynamics, ODE existence and uniqueness, stability, chaos, and
PDE theory remain proof-horizon material.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-dynamics-v0
cargo test -p axeyum-solver --test math_resource_lra_routes bounded_dynamics_bad_transition_step_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes bounded_dynamics_bad_threshold_step_artifact_emits_checked_farkas
```
