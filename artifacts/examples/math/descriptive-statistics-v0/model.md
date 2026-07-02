# Model

Finite samples are represented as exact rational strings. Contingency and
success tables are represented as nonnegative integer counts.

Example finite sample:

```json
{
  "sample": ["1", "2", "3", "4"],
  "mean": "5/2",
  "second_moment": "15/2",
  "population_variance": "5/4"
}
```

## Checks

### Mean And Variance

For the sample `[1, 2, 3, 4]`, the pack checks:

```text
mean = 5/2
E[X^2] = 15/2
Var(X) = E[X^2] - mean^2 = 5/4
```

This is population variance over the listed finite data, not an estimator.
The bad-variance replay row rejects the malformed `3/2` claim by recomputing
the exact statistic. The separate checked `qf-lra-bad-variance` row preserves
the proof boundary by recording `mean^2 = 25/4`, then letting QF_LRA/Farkas
reject the final contradiction:

```text
population_variance + 25/4 = 15/2
population_variance = 3/2
```

### Contingency Table Margins

For the table:

```text
[[8, 2],
 [1, 9]]
```

the pack checks row sums `[10, 10]`, column sums `[9, 11]`, and total `20`.
The promoted bad-total row turns the impossible claim `total = 19` into a
checked QF_LIA/Diophantine certificate.

### Simpson's Paradox

The pack checks a two-stratum integer-count witness:

```text
small: A = 81/87,  B = 234/270
large: A = 192/263, B = 55/80
total: A = 273/350, B = 289/350
```

`A` has a higher success rate in both strata, while `B` has a higher aggregate
success rate.

These fixed checks are exact arithmetic witnesses. They are not claims about
causal inference, random sampling, or model validity.

Certificate routes:

- exact rational infeasibility, such as contradictory mean or variance bounds,
  belongs on the QF_LRA/Farkas route;
- inconsistent integer margins or count equations belong on the
  QF_LIA/Diophantine route;
- satisfiable finite tables remain finite-model replay.
