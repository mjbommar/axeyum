# ADR-0191: Glaurung replay-SAT-cache measurement control

Status: accepted
Date: 2026-07-16

## Context

ADR-0189 fixes the evidence boundary for exact duplicate reuse, and ADR-0190
implements the disabled-by-default cache inside one arena-bound
`IncrementalBvSolver`. The remaining GQ8 question is empirical: does the cache
help Glaurung's ordered path-owned stream after mandatory original-term replay,
without changing verdicts, findings, memory behavior, or the accepted adaptive
warm default?

The client must expose a controlled experiment before a performance result can
answer that question. Enabling a cache in one-shot fallbacks, sharing it across
lineages, or treating strict prefixes as verdict hits would violate ADR-0189.
Aggregate timing without exact cache traffic would also repeat the earlier
fast-failure benchmark mistake.

## Decision

Accept Glaurung commit `d5475f6` as the downstream GQ8 measurement control, not
as production-cache admission.

The control has these boundaries:

- `GLAURUNG_AXEYUM_REPLAY_SAT_CACHE` is explicit and disabled when unset;
  only `on`, `true`, or `1` enables it, while invalid values fail closed to
  off;
- only path-owned `lineage`, `auto`, and `adaptive` sessions enable the cache;
  snapshot mode and every one-shot fallback remain cache-free;
- every live path owns an independent arena, incremental solver, and cache.
  Entries never move between paths, arenas, threads, processes, or artifacts;
- each path is deterministically bounded to 64 exact entries, 4,096 scalar
  model values, and 262,144 Bool/QF_BV payload bits. Glaurung's separate 9-live-
  path and 512-assertion ceilings remain in force;
- the process footer reports enablement, bounds, hits, misses, insertions,
  evictions, replay failures, declined result classes, and current entry/value/
  bit gauges. Terminal cleanup must return all gauges to zero;
- the versioned lineage runner accepts explicit cache-off/cache-on policies,
  requires every retained warm check to partition into a hit or miss, requires
  fresh misses to partition into inserted or declined results, rejects replay
  failures, requires exact cache traffic across repetitions, and preserves the
  existing verdict, unknown-split, finding, RSS, work-identity, and timing
  gates; and
- the comparator permits cache off to on only through a named flag and rejects
  any simultaneous warm-policy or other identity change.

Glaurung's accepted adaptive warm policy remains unchanged and the cache remains
off by default. A default may be reconsidered only after clean repeated
SurfacePen and fixed-budget NETwtw10 off/on artifacts pass the ordinary
3% Axeyum-time, 3% normalized-ratio, 5% median-RSS, and 2% absolute-Z3-drift
alarms with identical findings and exact work.

## Evidence

Focused Glaurung tests cover conservative policy parsing, exact SAT hits,
strict-extension misses, declined UNSAT results, cache-free ordinary snapshot
construction, footer parsing, traffic partitions, terminal-state cleanup, and
the named comparison transition. All 30 Axeyum-backend unit tests and all 13
lineage-runner tests pass. The dual-backend release example builds under the
4 GiB wrapper, and all three committed historical lineage artifacts remain
valid under the backward-compatible reader.

An explicitly dirty, one-process SurfacePen plumbing smoke decides and agrees
2,551/2,551 checks under both policies with zero unknown splits and identical
finding-output hashes. Cache off reports only zero counters. Cache on reports
183 replay-checked hits, 2,368 misses, 2,099 SAT insertions, 269 declined UNSAT
results, 832 deterministic evictions, zero replay failures, and zero live
entries/values/bits after all paths terminate. The 183 hits exceed the 121
consecutive exact snapshots because exact non-consecutive queries can recur
after scope changes inside the same path-owned solver.

The smoke's Axeyum time changes 1,089.6 to 1,060.4 ms and RSS changes 82,304 to
82,544 KiB, but this is not performance evidence: Z3 changes 4,575.9 to
4,423.7 ms (-3.33%), breaching the normal 2% environment alarm, and there is
only one process per policy. The run validates the control and accounting only.

## Consequences

GQ8 can now be measured end to end without weakening the framework's replay
boundary or changing Glaurung's production default. Exact cache traffic, not
just elapsed time, becomes required evidence. Prefix extensions continue to
reuse retained AIG/CNF/SAT state through GQ7 and never count as cache hits.

The immediate next step is the clean repeated two-driver off/on gate. A pass may
admit a downstream default in a new ADR; a regression, excessive eviction, or
insufficient hit rate keeps the cache explicit/off and guides a separately
measured capacity experiment. Cross-arena caches, cached ordinary UNSAT, and
proof-free prefix verdict reuse remain unauthorized.

## Alternatives

Enabling the cache immediately was rejected because the smoke is dirty,
single-process, and outside the Z3-drift alarm. A process-global SMT-LIB hash
cache was rejected by ADR-0189's identity and model-remapping requirements.
Enabling snapshot and one-shot paths was rejected because their ownership does
not provide the same arena-bound namespace. Raising bounds after observing 832
evictions was rejected because capacity is a measurement variable whose memory
and performance effects require a separate controlled gate.
