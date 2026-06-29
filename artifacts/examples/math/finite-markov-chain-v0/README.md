# Finite Markov Chain V0

This pack adds a finite stochastic-process slice for the probability,
linear-algebra, statistics, and dynamics lanes. It uses exact rational
transition matrices and finite distributions only.

The examples are:

- row-stochastic transition-matrix replay;
- finite-horizon distribution evolution for a three-state absorbing chain;
- stationary distribution replay for a two-state chain;
- checked rejection of a malformed transition row.

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

This is checked finite evidence for the bad transition-row claim and replay-only
evidence for the positive witnesses. The bad row is also tied to Axeyum's
`QF_LRA` route: the final row-sum contradiction must produce rechecked
`UnsatFarkas` evidence. Countably infinite Markov chains, mixing times,
convergence theorems, and stochastic-process limit theorems remain
Lean/proof-horizon material.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-markov-chain-v0
```
