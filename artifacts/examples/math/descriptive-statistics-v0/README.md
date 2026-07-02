# Descriptive Statistics V0

This pack covers exact finite descriptive statistics for the `statistics`
field-extension row. It uses rational arithmetic over fixed finite data and
integer count tables, not floating-point inference or sampling.

The examples are the statistics shadow that maps finite witnesses to replay
today and future invalid-claim rows to Axeyum's LRA/LIA certificate routes:

- mean and population variance identity for a small data set;
- exact replay rejection of an impossible population-variance claim plus a
  separate QF_LRA/Farkas certificate for the isolated linear contradiction;
- contingency-table row, column, and total margins;
- a QF_LIA/Diophantine certificate for an impossible contingency total;
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
variance, margins, and Simpson rate inequalities. The bad variance replay row
computes the finite sample statistic exactly; the separate `qf-lra-bad-variance`
row is emitted as a solver-form exact-rational contradiction and checked with
Farkas evidence. The promoted bad total row is emitted as a solver-form integer
margin contradiction and checked with Diophantine evidence.

Positive rows remain finite-model replay. Impossible exact-rational statistic
constraints should graduate through QF_LRA/Farkas certificates, and
inconsistent integer margin or count constraints should graduate through
QF_LIA/Diophantine certificates. The pack still does not treat statistical
inference, floating-point estimation, MCMC, or model calibration as proof.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/descriptive-statistics-v0
```
