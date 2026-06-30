# Finite Random Variables V0

This pack adds exact finite random-variable checks. It treats a random variable
as a total finite function from probability atoms to outcome labels, then checks
pushforward distributions, expectations, independence, and a checked rejection
of a false pushforward claim.

The examples are:

- a pushforward distribution witness;
- an expectation-through-pushforward witness;
- an independent random-variables witness;
- checked rejection of a false pushforward distribution;
- a general random-variable and conditional-expectation Lean-horizon row.

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

The validator checks normalized finite atom probabilities, verifies that each
random variable is total on the atom set, recomputes pushforward probability
mass by exact summation, recomputes expectation both from atoms and from the
pushforward distribution, and checks independence by comparing a joint
distribution to the product of its marginals. The false pushforward row is also
mirrored by a QF_LRA/Farkas regression over the replay-computed outcome mass.

This pack is checked finite evidence for the bad pushforward row. It is not a
proof of general measurable-function theory, conditional expectation,
martingales, stochastic kernels, or continuous random variables.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-random-variables-v0
```
