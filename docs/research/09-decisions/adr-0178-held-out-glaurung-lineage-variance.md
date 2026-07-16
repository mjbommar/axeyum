# ADR-0178: Held-out Glaurung lineage variance

Status: accepted
Date: 2026-07-15

## Context

ADR-0177 raises the explicit Glaurung lineage assertion ceiling to 512 from one
held-out SurfacePen profile and one bounded NETwtw10 stress process. It requires
repetition before GQ9 may treat 9/512 as more than a first held-out result.

Wall-clock analysis cutoffs cannot provide that repetition: the first two
60-second NETwtw10 processes execute 23,797 and 22,132 queries. Both are sound
diagnostics, but timing totals over different query counts are not variance
evidence. A fixed work boundary is required.

## Decision

Accept 9 live sessions and 512 assertions as the bounded explicit-lineage
envelope across every currently available Glaurung realworld driver that issues
solver queries, using repeated SurfacePen and fixed-budget NETwtw10 tiers.

- NETwtw10 repetition uses `IOCTLANCE_SOLVE_BUDGET=20000`, a 400-second
  analysis deadline, the existing 600-second solver budget, and the hard 4 GiB
  process cap. A wall-cutoff process is never mixed into the variance tier.
- Every repetition must preserve the exact query count and lifecycle/root/
  fallback counters, decide and agree every occurrence, and finish with zero
  live sessions and resets.
- This accepts only the resource envelope after explicit lineage selection. It
  does not set `GLAURUNG_AXEYUM_WARM_REUSE` implicitly, authorize GQ8 caching,
  weaken model/proof replay, or turn diagnostic profile time into a performance
  bar.

## Evidence

SurfacePen runs three default-policy processes. All execute the same 2,551
queries and identical traffic: 121 exact snapshots, 290,670 prefix roots,
19,467 added roots, 147 popped roots, 358 created/closed sessions, peak four,
and zero fallbacks/resets. All 7,653 occurrences agree with Z3.

| SurfacePen metric | Result |
|---|---:|
| Mean Axeyum | 1,069.4 ms |
| Mean Z3 | 4,409.0 ms |
| Axeyum/Z3 | 0.243x |
| Axeyum population CV | 0.34% |
| Median RSS | 83,140 KiB |

The fixed-budget NETwtw10 tier also runs three processes. Every process executes
exactly 28,356 queries with the same 20,031 retained checks, 1,285 exact
snapshots, 529,071 prefix roots, 247,311 added roots, 2,228 popped roots, 5,961
created/closed sessions, peak nine, 8,325 path fallbacks, zero assertion
fallbacks, and zero resets. All 85,068 occurrences agree with Z3.

| NETwtw10 metric | Result |
|---|---:|
| Mean Axeyum | 18,770.6 ms |
| Mean Z3 | 52,085.8 ms |
| Axeyum/Z3 | 0.360x |
| Axeyum population CV | 0.44% |
| Median RSS | 257,736 KiB |
| RSS range | 257,512--257,996 KiB |

The large tier deliberately retains its 8,325 one-shot path-cap fallbacks:
ADR-0177's cap-12 comparison recovers only 417 checks and 1.5% Axeyum time for
about 10 MiB more RSS. Assertion fallback remains zero. The exact repeated
traffic demonstrates that the fixed budget, not a wall cutoff, defines stable
work.

The remaining held-out pciidex sample issues no solver queries. Together with
ADR-0176's original repeated vwififlt/Dptf/IntcSST tier, every one of the six
available realworld samples is now exercised and every observed query stream is
covered by repeated evidence. Glaurung `eb938ae` records the recipes and bars.

## Alternatives

Treating the two 60-second Wi-Fi processes as repeats was rejected because the
query counts differ by 7%. Increasing only the wall deadline was rejected as a
machine-load-dependent work definition. Removing the live cap to make all work
warm was rejected by the measured RSS tradeoff. Automatic warm selection was
rejected because the available tier validates a fixed explicit envelope, not a
topology/cost classifier or behavior on unseen families.

## Consequences

The immediate GQ10 held-out repetition gate is complete. Current production
guidance is precise: Glaurung users may explicitly select lineage reuse with the
bounded 9/512 default, visible fallbacks, and unchanged replay/proof semantics.

Next automate the fixed-policy per-commit artifact so source revision,
environment, driver, limits, exact work counters, time, and RSS are compared
fail-closed. Add newly available driver families when captured. GQ9 automatic
selection remains gated on a telemetry-visible topology/cost rule validated
against that automated held-out tier; GQ8 still needs a separate cache identity,
capacity, invalidation, and replay ADR.
