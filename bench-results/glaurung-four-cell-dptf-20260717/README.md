# Glaurung DptfDevGen four-cell fair baseline

- Date: 2026-07-17
- Glaurung revision: `4ae96cfd06a1abb72d1c3977f2dfd878680a9739`
  (clean detached worktree)
- Axeyum solver revision: `ba7ec9a2` (solver sources unchanged during capture;
  the v2 analyzer/docs increment was uncommitted)
- Driver SHA-256:
  `074be1b90deb21897538a6b093af9826e62610ffd878c92289af31c5ca3f724b`

This is the first clean exercise of ADR-0215's topology-equivalent control.
Every authoritative cold-Z3 occurrence independently times four cells in
rotating order: Z3 cold, Z3 retained direct lineage, Axeyum cold, and Axeyum
retained direct lineage. Both warm cells use the same source owner, serial
sibling lease, exact source-prefix LCP, and temporary-assumption partition.

Five sequential fresh-process runs used a predeclared 60-second per-function
solver bound. Every run has the same 561 ordered checks. All four cells decide
all 561 with no operational result, decided disagreement, replay failure, or
fallback. Both warm populations are exactly 7 `warm-created` plus 554
`warm-retained` checks (98.7522% retained).

| Paired contrast | Per-occurrence geomean | Bootstrap 95% CI | Per-run geomean CV |
|---|---:|---:|---:|
| Z3 cold / Axeyum cold | 0.9661x | [0.8709, 1.0706] | 1.6653% |
| Z3 warm / Axeyum warm | 0.7875x | [0.6893, 0.8977] | 0.9950% |
| Z3 cold / Z3 warm | 8.9752x | [8.5511, 9.4112] | 0.8895% |
| Axeyum cold / Axeyum warm | 7.3157x | [6.4477, 8.2741] | 1.6002% |

Ratios are numerator/denominator, so the fair warm result favors Z3: retained
Z3 takes about 0.7875x Axeyum's latency, or Axeyum is about 1.27x slower on
this easy driver. The cold-vs-cold interval crosses parity. Both solvers gain
substantially from the same retained topology, with a larger measured benefit
for Z3 here. This directly invalidates the old cold-Z3/warm-Axeyum scalar as a
solver headline: that legacy alias is 7.0678x [6.2136, 8.0555], but it mostly
compares session policies.

Median per-occurrence latencies are:

| Cell | p50 | p90 | p95 | p99 |
|---|---:|---:|---:|---:|
| Z3 cold | 1104.906 us | 2882.397 us | 3395.155 us | 5005.868 us |
| Z3 warm | 140.395 us | 265.428 us | 326.565 us | 502.518 us |
| Axeyum cold | 1970.224 us | 5266.021 us | 6206.758 us | 7427.404 us |
| Axeyum warm | 170.876 us | 1347.246 us | 1764.267 us | 3717.306 us |

The scalar is the geometric mean of per-occurrence paired ratios after each
occurrence is collapsed across five repetitions. It is not a ratio of summed
times. [`report.json`](report.json) contains every comparison, confidence
interval, quantile, process CV, exact configuration identity, and raw-trace
pointer. The `cdf/` directory contains both legacy two-cell and explicit
four-cell CSV/PNG latency distributions.

Artifact SHA-256 values:

- `report.json`:
  `dd91696a4bff32adce105739cbc94abdb84c767491de2a18531500e19e527544`
- `cdf/sqfs-intel-DptfDevGen.sys-four-cell-latency-cdf.csv`:
  `e6eb238756e82b4e5c08d04265fa5dda91df6cad7ee96f8c1eb31255045fc7b4`
- `cdf/sqfs-intel-DptfDevGen.sys-four-cell-latency-cdf.png`:
  `89acd8e74dba22560b6063d026defad1456e6b52c2dc0c7768c8fffee50a40dc`

The 45 MiB raw restricted-driver traces are retained outside git at
`/nas4/data/workspace-infosec/.axeyum-fair-dptf-20260717.ukI3zk`. Each trace
passes Glaurung's independent v2 structural validator with 2,489 events, 133
paths, 377 unique queries, 316 assertions, 561 checks, and 166 model reads.

This is one easy-driver control, not a general solver conclusion. A neutral
solver, timeout-sensitive driver, additional workloads, and authoritative
finding parity remain required by ADR-0213.
