# Descriptive Statistics V0

This pack covers exact finite descriptive statistics for the `statistics`
field-extension row. It uses rational arithmetic over fixed finite data and
integer count tables, not floating-point inference or sampling.

The examples are the statistics shadow that maps finite witnesses to replay
today and future invalid-claim rows to Axeyum's LRA/LIA certificate routes:

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
variance, margins, and Simpson rate inequalities.

Current rows are satisfiable witnesses, so finite-model replay is the checked
evidence. Future impossible exact-rational statistic constraints should
graduate through QF_LRA/Farkas certificates, and inconsistent integer margin or
count constraints should graduate through QF_LIA/Diophantine certificates. The
pack still does not treat statistical inference, floating-point estimation,
MCMC, or model calibration as proof.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/descriptive-statistics-v0
```
