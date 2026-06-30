# Finite Martingales V0

This pack adds exact finite martingale checks. It treats a filtration as a
time-indexed sequence of finite partitions of probability atoms and checks
adaptedness, martingale conditional-expectation equalities, a square
submartingale witness, and a bounded stopping-time replay.

The examples are:

- a finite martingale witness for a two-step fair walk;
- a square-submartingale witness;
- a bounded optional-stopping replay row;
- checked rejection of a false martingale claim;
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

This pack is checked finite evidence for the bad martingale row. It is not a
proof of general martingale convergence, optional stopping, Doob inequalities,
or stochastic integration. The malformed martingale row is also mirrored by a
source-linked QF_LRA/Farkas regression after finite replay computes the
conditional expectation.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-martingales-v0
```
