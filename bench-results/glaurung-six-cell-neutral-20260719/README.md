# Glaurung six-cell neutral warm regime

This directory began as ADR-0272's **zero-result-row registration**. The
mechanism, v3 consumer, exact release executable, driver population, runtime
linkage, run order, statistical contrasts, and acceptance gates were frozen
before any real-driver v3 timing row was observed.

- Registration: [`registration.json`](registration.json)
- Preregistration: [ADR-0272](../../docs/research/09-decisions/adr-0272-preregister-six-cell-neutral-warm-regime.md)
- Glaurung producer: `2961d7c1bca03f14b77b12fb852d193413207982`
- Axeyum v3 analyzer: `5d74283b8cc1779df4d67b654c44d6b7dcc94611`
- Fail-closed campaign runner:
  [`scripts/run-glaurung-six-cell-neutral.py`](../../scripts/run-glaurung-six-cell-neutral.py),
  SHA-256 `daeec160c41862e3a70cc216831971a402d8b7392e3e6b60504b2503e89fbc7c`
- Release executable SHA-256:
  `5d454daf6c12c1d69bc0e28e12c391286b53d1a7735514043b85ea82057ef17b`

At registration time there were no trace paths, timing values, ratios,
confidence intervals, or driver conclusions in this directory. That historical
boundary remains in `registration.json`.

## Accepted result

The exact driver-major campaign completed all 20 fresh processes. Every process
published one producer-validated v3 trace. Across one four-driver pass there are
12,902 checks (10,647 SAT and 2,255 UNSAT); five repetitions therefore contain
64,510 ordered occurrences and 387,060 measured solver-cell executions. Every
cell decides every occurrence with the same verdict. There are zero unknowns,
operational errors, decided disagreements, replay failures, or warm fallbacks.
All three warm populations have identical created/retained membership:

| Driver | Checks/run | SAT/UNSAT | Warm created/retained | All-six gate |
|---|---:|---:|---:|---|
| DptfDevGen | 603 | 387 / 216 | 7 / 596 | accepted |
| vwififlt | 5,182 | 3,589 / 1,593 | 14 / 5,168 | accepted |
| IntcSST | 2,309 | 2,028 / 281 | 24 / 2,285 | accepted |
| SurfacePen | 4,808 | 4,643 / 165 | 43 / 4,765 | accepted |

Ratios are numerator latency divided by denominator latency; greater than one
favors the denominator. The warm map is:

| Driver | Z3/Axeyum warm (95% CI) | Z3/Bitwuzla warm (95% CI) | Axeyum/Bitwuzla warm (95% CI) |
|---|---:|---:|---:|
| DptfDevGen | 0.8448 [0.7368, 0.9692] | 1.6158 [1.5080, 1.7327] | 1.9126 [1.7051, 2.1461] |
| vwififlt | 1.0523 [1.0190, 1.0879] | 1.6914 [1.6691, 1.7140] | 1.6073 [1.5579, 1.6578] |
| IntcSST | 2.2321 [2.1243, 2.3408] | 2.4422 [2.3810, 2.5075] | 1.0941 [1.0490, 1.1398] |
| SurfacePen | 2.2819 [2.2213, 2.3452] | 3.9066 [3.8349, 3.9797] | 1.7120 [1.6739, 1.7509] |

The neutral result is unambiguous: warm Bitwuzla is fastest on all four
drivers. Axeyum still has a workload-dependent advantage over warm Z3—wins on
vwififlt, IntcSST, and SurfacePen, and a loss on DptfDevGen—but is not the
performance leader against the neutral implementation. The result supports a
rigorously characterized regime, not an Axeyum speed headline.

Cold ordering is also workload-dependent. Bitwuzla is fastest on DptfDevGen
and vwififlt, while Axeyum is fastest on IntcSST and SurfacePen. All three
solvers benefit materially from retained topology:

| Driver | Z3 cold/warm | Axeyum cold/warm | Bitwuzla cold/warm |
|---|---:|---:|---:|
| DptfDevGen | 8.1691 | 5.9613 | 7.3834 |
| vwififlt | 5.6011 | 8.4781 | 8.3017 |
| IntcSST | 6.6750 | 5.3471 | 8.6268 |
| SurfacePen | 7.6520 | 6.7650 | 18.0561 |

These are paired per-occurrence geomeans, never ratios of sums. The three
preregistered primary warm-pair process CVs are below 1.86% on every driver.
The exact reports contain all nine contrasts, bootstrap intervals, quantiles,
per-run variance, execution populations, configuration identity, and CDF data.
An independent same-input analyzer rerun reproduced all four report files
byte-for-byte.

- [`result-summary.json`](result-summary.json)
- [`dptf/report.json`](dptf/report.json)
- [`vwififlt/report.json`](vwififlt/report.json)
- [`intcsst/report.json`](intcsst/report.json)
- [`surfacepen/report.json`](surfacepen/report.json)

Raw traces and logs remain outside git at
`/nas4/data/workspace-infosec/.axeyum-six-cell-20260719.AjDth1` (1.4 GiB). Its
`campaign.json` SHA-256 is
`cf1c7f59ccf9faf6fc398ddfd668331d32b1bdb69a7d7e5c51c348480a3bb50b`.
