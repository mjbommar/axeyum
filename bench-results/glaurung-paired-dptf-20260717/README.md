# Glaurung DptfDevGen paired-trace mechanism exercise

- Date: 2026-07-17
- Glaurung revision: `eb624c087baf4d8409e2b9a2c009dd93cb15981c`
  (clean detached worktree)
- Axeyum solver revision: `ee1bc306` (solver sources clean; this analysis/docs
  increment was uncommitted during capture)
- Driver SHA-256:
  `074be1b90deb21897538a6b093af9826e62610ffd878c92289af31c5ca3f724b`

This is the first real-driver exercise of ADR-0214's paired measurement
mechanism. It is a fixed-work no-timeout control, not a paper-level solver
comparison: Z3 is still the cold one-shot FFI baseline, Axeyum is warm, the
driver produces no timeout split in any cell, and only one driver/query
distribution is represented.

Each `{1, 5, 60}`-second cell contains five sequential fresh-process runs.
Every run has the same 561 ordered checks, all 561 are decided by both backends,
and there are zero Z3-only, Axeyum-only, neither-decided, operational-error,
replay-failure, or decided-disagreement rows. The execution population is
stable at 7 `warm-created` plus 554 `warm-retained` checks: 100% pure-warm
execution and 98.7522% retained-warm execution, with no named fallback.

| Timeout | Paired geomean Z3/Axeyum | Bootstrap 95% CI | Per-run geomean CV | Z3 p50 | Axeyum p50 |
|---:|---:|---:|---:|---:|---:|
| 1 s | 5.9771x | [5.3341, 6.7167] | 1.8037% | 596.755 us | 95.393 us |
| 5 s | 6.0953x | [5.4429, 6.8513] | 0.7836% | 603.515 us | 95.194 us |
| 60 s | 6.0128x | [5.3662, 6.7548] | 1.5977% | 591.492 us | 97.234 us |

The scalar is the geometric mean of per-occurrence paired ratios after each
occurrence is collapsed across repetitions. It is intentionally not the
different ratio-of-summed-times printed by Glaurung's diagnostic footer.

Each timeout directory contains the exact analyzer JSON plus its latency-CDF
CSV and PNG. Report SHA-256 values are:

- `1s/report.json`: `ebab4f591cd0183cfa100436ad33a6eb842e5931551bde4a00278201af53f23f`
- `5s/report.json`: `79d8d5e28ee971cbaad687b825dcc70ab7cff2c50eae7c1c66bac6d36a19619b`
- `60s/report.json`: `fa2e8106104ba3cb9f989ffe9a637ed1620effa942800436fe81a9346a387c0c`

The 133 MiB raw restricted-driver trace set is not committed. It is retained at
`/nas4/data/workspace-infosec/.axeyum-paired-dptf-20260717`; the relative
`trace_paths` in each report resolve from that directory. Reanalysis from the
retained copy reproduced all three committed JSON reports byte-for-byte.
