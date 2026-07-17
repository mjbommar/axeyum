# Glaurung bounded-warm time/RSS Pareto

- Date: 2026-07-17
- Axeyum revision: `629c16338a9aa0f4ac9f4f249e1b21300996ca15`
- Glaurung revision: `4fce79fccd167c898fa5acad24f4b8b947ba7daa`
- Report SHA-256: `fe0d674cf909dc7c7628a00ff466784c0e27184c5f1055ff4ce5f442d31ef252`
- Repetitions: five per policy and driver, order balanced
- Explorer authority: Z3

This control measures the complete bounded adaptive policy against explicit
one-shot Axeyum in separate processes. Both policies receive the same
Z3-authoritative exploration stream. Every query verdict agrees, finding
counts are invariant, all warm lifecycle gauges close, and there are no
fallbacks, resets, or replay failures.

| Driver | Queries/run | One-shot Axeyum | Adaptive Axeyum | Total-work ratio | One-shot RSS | Adaptive RSS | Paired RSS delta | Retained-owner hits |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| DptfDevGen | 561 | 998.9 ms | 146.6 ms | 6.829x | 59,600 KiB | 75,040 KiB | +25.58% | 554/561 (98.75%) |
| SurfacePen | 2,551 | 1,397.8 ms | 255.7 ms | 5.465x | 65,300 KiB | 74,624 KiB | +14.77% | 2,508/2,551 (98.31%) |

The time column is cumulative same-stream Axeyum work. It is useful for the
deployment-policy Pareto but is not a paired per-occurrence solver speedup and
must not replace ADR-0215/0217's four-cell statistics. Process elapsed medians
also improve from 1.55 to 0.70 seconds on Dptf and 5.88 to 4.82 seconds on
SurfacePen, where the unchanged authoritative Z3 work limits the wall-time
gain.

Memory is first-class rather than hidden in a footnote. Adaptive reuse costs a
measured 14.77% median RSS on SurfacePen and 25.58% on Dptf. The Dptf one-shot
RSS population has 9.20% CV, so its overhead magnitude is noisy even though all
five paired ratios remain above one; SurfacePen is the cleaner memory result at
1.75%/0.41% one-shot/adaptive RSS CV.

Warm-hit accounting is explicit. Dptf creates seven owners and retains 554
checks, with 130 replay-cache hits and 431 actual core calls. SurfacePen creates
43 owners and retains 2,508 checks, with 178 cache hits and 2,373 core calls.
Neither driver exercises a capacity fallback, so this is a high-reuse regime,
not evidence for workloads that churn the bounded owner pool.

Exact arrays, configuration, hashes, counts, and exclusions are in
[`report.json`](report.json). The reusable fail-closed runner is
`scripts/measure-glaurung-warm-rss.py`.
