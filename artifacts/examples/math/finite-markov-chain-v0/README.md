# Finite Markov Chain V0

This pack adds a finite stochastic-process slice for the probability,
linear-algebra, statistics, and dynamics lanes. It uses exact rational
transition matrices and finite distributions only.

The examples are:

- row-stochastic transition-matrix replay;
- finite-horizon distribution evolution for a three-state absorbing chain;
- stationary distribution replay for a two-state chain;
- replay-only rejection of a malformed transition row and a false stationary
  distribution;
- separate checked `QF_LRA`/Farkas rows for the isolated scalar conflicts.

## Concepts

- `field_probability_theory`
- `field_linear_algebra`
- `field_differential_equations_and_dynamical_systems`
- `field_statistics`
- `curriculum_counting`
- `curriculum_rationals`
- `curriculum_linear_algebra`

## Trust Story

The validator parses transition probabilities and distribution entries as exact
rational strings. It checks row sums, nonnegativity, distribution normalization,
row-vector matrix multiplication, absorption probability at a fixed horizon, and
stationarity.

This is exact finite replay for the positive witnesses and the malformed
transition/stationary rows. Separate `qf-lra-*` rows tie the final row-sum and
stationary-coordinate contradictions to Axeyum's `QF_LRA` route; those rows
must produce rechecked `UnsatFarkas` evidence. Countably infinite Markov chains,
mixing times, convergence theorems, and stochastic-process limit theorems
remain Lean/proof-horizon material.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-markov-chain-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_markov_chain_bad_stochastic_row_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_markov_chain_bad_stationary_distribution_artifact_emits_checked_farkas
```
