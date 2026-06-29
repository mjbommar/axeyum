# Generating Functions V0

This pack deepens the `counting`, `polynomials`, and `sequences-and-limits`
curriculum rows with finite ordinary generating-function checks. It treats a
finite prefix of a sequence as an exact polynomial of coefficients, so every
claim is replayed by deterministic rational polynomial arithmetic.

The pack covers:

- coefficient extraction from an ordinary generating polynomial;
- Cauchy product replay as finite convolution;
- a bounded Fibonacci generating-function prefix identity;
- checked rejection of a bad convolution coefficient;
- a Lean-horizon row for general generating-function theory.

## Concepts

- `curriculum_counting`
- `curriculum_polynomials`
- `curriculum_sequences_and_limits`
- `field_discrete_math`
- `field_abstract_algebra`
- `field_probability_theory`
- `field_real_analysis`

## Trust Story

The validator parses every coefficient as an exact rational string. It
recomputes polynomial products, finite convolutions, recurrence prefixes, and
the explicit bad coefficient without floating point.

This is a finite prefix replay pack. It does not claim closed-form extraction,
analytic convergence, asymptotics, or general recurrence-solving theorems.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/generating-functions-v0
```
