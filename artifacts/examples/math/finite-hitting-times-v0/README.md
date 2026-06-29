# Finite Hitting Times V0

This pack adds exact finite hitting-time checks for small Markov chains. It
uses a finite absorbing chain and checks first-hit probabilities over a bounded
horizon, absorption-probability equations, expected hitting-time equations, and
a malformed expected-time table.

The examples are:

- a first-hit distribution and survival replay through horizon `4`;
- an absorption-probability equation witness;
- an expected hitting-time equation witness;
- checked rejection of a false expected hitting-time table;
- a recurrence, transience, and optional-stopping Lean-horizon row.

## Concepts

- `field_probability_theory`
- `field_differential_equations_and_dynamical_systems`
- `field_linear_algebra`
- `field_statistics`
- `field_measure_theory`
- `field_set_theory_and_foundations`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_counting`
- `curriculum_rationals`
- `curriculum_linear_algebra`

## Trust Story

The validator checks a finite row-stochastic transition matrix, replays
first-hit probabilities by moving only non-hit mass forward, checks survival
probability after the listed horizon, verifies absorption probabilities as a
finite linear fixed-point table, and verifies expected hitting times as exact
linear equations.

This pack is checked finite evidence for the bad expected-time row. It is not a
proof of recurrence/transience classifications, infinite-horizon convergence,
mixing, optional stopping, or general Markov-chain potential theory.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-hitting-times-v0
```
