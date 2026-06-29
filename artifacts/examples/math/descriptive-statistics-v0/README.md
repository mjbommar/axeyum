# Descriptive Statistics V0

This pack covers exact finite descriptive statistics for the `statistics`
field-extension row. It uses rational arithmetic over fixed finite data and
integer count tables, not floating-point inference or sampling.

The examples are the statistics shadow that will later map to Axeyum's LRA,
LIA, and finite-enumeration routes:

- mean and population variance identity for a small data set;
- contingency-table row, column, and total margins;
- Simpson's paradox witness from integer success/total counts.

## Concepts

- `field_statistics`
- `field_probability_theory`
- `field_linear_algebra`
- `curriculum_rationals`
- `curriculum_counting`
- `curriculum_linear_algebra`

## Trust Story

The current validator parses all scalar statistics exactly as rational strings
and count tables as integers. It recomputes the mean, second moment, population
variance, margins, and Simpson rate inequalities. It does not yet emit SMT-LIB,
call Axeyum's LRA/LIA routes, or treat statistical inference, floating-point
estimation, MCMC, or model calibration as proof.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/descriptive-statistics-v0
```
