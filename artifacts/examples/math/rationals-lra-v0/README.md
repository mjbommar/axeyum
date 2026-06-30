# Rationals LRA V0

This pack covers exact rational arithmetic for the `rationals` curriculum node.
It uses small fixed witnesses and exact replay, not floating point.

The examples are the ordered-field shadow that will later map to Axeyum's LRA
route and Farkas evidence:

- density between two rationals;
- additive inverse;
- trichotomy for a fixed pair, with Farkas-checked impossible branches;
- order transitivity for a fixed chain, with a Farkas-checked violating branch.

## Concepts

- `curriculum_rationals`
- `curriculum_reals`
- `field_real_analysis`
- `field_linear_algebra`

## Trust Story

The validator parses fraction strings exactly with Python rational arithmetic
and checks the listed equalities/inequalities. The two fixed `unsat` order rows
also have an Axeyum regression that builds the corresponding `QF_LRA` formulas,
emits `UnsatFarkas` evidence, and rechecks that evidence independently. Those
rows now also carry source-level SMT-LIB artifacts that the route regression
parses before checking Farkas evidence. This is not a general theorem of
rational order theory; it is checked evidence for the fixed rows.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rationals-lra-v0
cargo test -p axeyum-solver --test math_resource_lra_routes rationals
```
