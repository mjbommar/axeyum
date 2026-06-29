# Rationals LRA V0

This pack covers exact rational arithmetic for the `rationals` curriculum node.
It uses small fixed witnesses and exact replay, not floating point.

The examples are the ordered-field shadow that will later map to Axeyum's LRA
route and Farkas evidence:

- density between two rationals;
- additive inverse;
- trichotomy for a fixed pair;
- order transitivity for a fixed chain.

## Concepts

- `curriculum_rationals`
- `curriculum_reals`
- `field_real_analysis`
- `field_linear_algebra`

## Trust Story

The current validator parses fraction strings exactly with Python rational
arithmetic and checks the listed equalities/inequalities. It does not yet emit
SMT-LIB, call Axeyum's LRA engine, or check Farkas certificates.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rationals-lra-v0
```
