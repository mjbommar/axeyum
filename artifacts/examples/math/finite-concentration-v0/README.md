# Finite Concentration V0

This pack adds exact finite concentration checks. It treats Markov's
inequality, Chebyshev's inequality, and the union bound as finite rational
table replays over explicitly listed probability atoms.

The examples are:

- a Markov inequality witness for a nonnegative finite random variable;
- a Chebyshev inequality witness for a finite centered variable;
- a union-bound witness for two finite events;
- checked rejection of a false concentration bound;
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
exact rational arithmetic. The bad-bound row is checked by recomputing the
actual tail probability and confirming it exceeds the claimed bound.

This pack is finite checked evidence. It is not a proof of general
concentration theory, laws of large numbers, central limit theorems,
martingale inequalities, or asymptotic statistics.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-concentration-v0
```
