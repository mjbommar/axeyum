# ADR-0228: Glaurung bounded-warm time/RSS Pareto

Status: accepted
Date: 2026-07-17

## Context

The publication review requires cold-path honesty, a visible memory tradeoff,
and the fraction of real checks that actually reuse retained state. The
four-cell evidence in ADR-0215/0217 measures paired per-occurrence latency and
warm execution classes, but its processes execute all four cells and therefore
do not isolate one-shot versus warm process RSS.

Older policy-selection records show material RSS costs, but merging their
memory numbers with the current fair timings would create a cross-revision
Pareto that no process actually measured. A separate current-revision,
same-stream, order-balanced control is required.

## Decision

Add a fail-closed runner that compares explicit one-shot Axeyum with the
complete bounded adaptive policy in separate Glaurung processes. Keep Z3
authoritative so both policies receive fixed exploration work. Accept a driver
only when every repetition preserves query count, verdict agreement, finding
counts, resource identity, zero capacity fallback, zero replay failure, and
closed lifecycle gauges.

Measure five order-balanced repetitions on DptfDevGen and SurfacePen. Report
cumulative same-stream Axeyum time beside process maximum RSS and exact owner,
cache, and core-call partitions. Treat the time ratio as a whole-policy
engineering metric, not a paired per-occurrence solver speedup. ADR-0215/0217
remain authoritative for Z3/Axeyum performance claims.

## Evidence

At Axeyum `629c1633` and clean Glaurung `4fce79f`, all 31,120 policy/check
executions agree with Z3 and preserve per-driver finding counts:

| Driver | Checks/run | One-shot Axeyum | Adaptive Axeyum | Total-work ratio | One-shot RSS | Adaptive RSS | Paired RSS delta |
|---|---:|---:|---:|---:|---:|---:|---:|
| DptfDevGen | 561 | 998.9 ms | 146.6 ms | 6.829x | 59,600 KiB | 75,040 KiB | +25.58% |
| SurfacePen | 2,551 | 1,397.8 ms | 255.7 ms | 5.465x | 65,300 KiB | 74,624 KiB | +14.77% |

Adaptive Axeyum time CV is 1.02%/1.04%. SurfacePen's RSS populations are also
stable at 1.75% one-shot and 0.41% adaptive CV. Dptf's one-shot RSS CV is
9.20%, so its positive overhead direction repeats five times but the magnitude
is noisier and must be reported as such.

Dptf retains 554/561 checks (98.75%), creates seven owners, serves 130 checks
from replay cache, and makes 431 core calls. SurfacePen retains 2,508/2,551
(98.31%), creates 43 owners, serves 178 cache hits, and makes 2,373 core calls.
Both record zero fallback, reset, replay failure, or terminal owner/reference
leak.

Exact arrays, hashes, configurations, and exclusions are committed under
[`bench-results/glaurung-warm-rss-pareto-20260717/`](../../../bench-results/glaurung-warm-rss-pareto-20260717/README.md).

## Consequences

The publication can show an explicit time/memory policy Pareto instead of
reporting warm latency alone: the accepted high-reuse policy materially reduces
Axeyum work while increasing process RSS by a measured 14.77% on the stable
SurfacePen control and a noisier 25.58% on Dptf. It must also report that more
than 98% of checks retain an owner and that neither control exercises fallback;
the result does not generalize to owner-churn workloads.

The one-shot result is no longer hidden, but its cumulative timer remains
different from the four-cell per-occurrence statistic. Do not use a ratio of
these totals as the paper's solver-speed headline. A four-driver matched RSS
distribution is optional widening; authoritative-Axeyum finding parity and a
real-query proof denominator remain higher-priority blockers.

## Alternatives

- Attach ADR-0171's RSS to ADR-0217's timing: rejected because revisions,
  policies, and process boundaries differ.
- Measure RSS with all four fair cells enabled: rejected because the process
  high-water mark cannot be assigned to one policy.
- Hide one-shot because production defaults warm: rejected because it obscures
  cold deployment cost and the memory paid for reuse.
- Call cumulative Axeyum time a per-query speedup: rejected; only the matched
  four-cell analysis supports that claim shape.
