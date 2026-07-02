# Finite Random Variables V0

This pack adds exact finite random-variable checks. It treats a random variable
as a total finite function from probability atoms to outcome labels, then checks
pushforward distributions, expectations, independence, replayed rejection of
false pushforward and expectation claims, and checked final QF_LRA/Farkas
contradictions for those false claims.

The examples are:

- a pushforward distribution witness;
- an expectation-through-pushforward witness;
- an independent random-variables witness;
- replay rejection of a false pushforward distribution;
- a checked QF_LRA/Farkas contradiction for the false pushforward claim;
- replay rejection of a false expectation-through-pushforward claim;
- a checked QF_LRA/Farkas contradiction for the false expectation claim;
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
distribution to the product of its marginals. The false pushforward and false
expectation replay rows compute the actual values; the separate
`qf-lra-bad-pushforward` and
`qf-lra-bad-expectation-through-pushforward` rows own the QF_LRA/Farkas
regressions over the replay-computed outcome mass and expectation.

This pack is checked finite evidence plus checked final linear contradictions
for the bad pushforward and bad expectation rows. It is not a proof of general
measurable-function theory, conditional expectation, martingales, stochastic
kernels, or continuous random variables.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-random-variables-v0
```
