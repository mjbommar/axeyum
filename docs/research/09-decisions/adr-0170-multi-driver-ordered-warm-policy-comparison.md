# ADR-0170: Multi-driver ordered warm-policy comparison

Status: accepted
Date: 2026-07-15

## Context

ADR-0169 selected consecutive snapshot/LCP reuse on one bounded Glaurung
driver: it reached 0.590x the same-stream Z3 time, while the deliberately naive
per-lineage control reached only 1.598x. That result proved structural headroom
but could not justify a product policy. Both formula cost and fork topology can
change across drivers, and the first sample's observed scope-depth threshold
was descriptive rather than causal.

The first wider capture attempt also exposed two downstream producer defects.
Glaurung evaluated an empty/default model after a non-SAT check, and extension
nodes could declare a source width inconsistent with their child. The trace
validator and Axeyum's strict parser correctly rejected those artifacts. The
producer was repaired rather than weakening either boundary: model-driven
execution now requires SAT, and extension children are explicitly coerced to
their declared source width in the renderer and both native adapters.

Glaurung remains an opt-in downstream workload and untrusted corpus producer.
Neither its trace schema nor its exploration policy becomes part of Axeyum's
formal-reasoning product architecture.

## Decision

Accept a clean, same-producer-revision three-driver comparison as bounded GQ7
and GQ10 evidence, with these conclusions:

1. reject snapshot/LCP as a universally winning warm policy;
2. retain both consecutive-snapshot and explicit-lineage controls as opt-in
   policies until the native client boundary and repeated-process variance are
   measured;
3. prioritize native per-lineage ownership/delta assertion because it wins the
   weighted bounded suite and two of three drivers, while retaining snapshot as
   the measured fallback for streams where fork reconstruction is expensive;
4. do not use scope depth alone as an admission rule; record online topology,
   prefix-retention, fork-root replay, formula-cost, latency, and memory signals
   before GQ9 chooses a policy; and
5. keep GQ8 verdict/CNF caching downstream of the retained-state integration
   and its replay/invalidation contract.

Every policy continues to require strict artifact identity, exact occurrence
order, 100% decided outcomes, verdict agreement, original-query model replay,
and explicit accounting for alternative satisfying model choices. A weighted
sum across the three bounded streams is descriptive workload evidence, not a
population estimate or a variance result.

## Evidence

All three traces were produced from clean Glaurung revision `dbdc6bf` with the
same five-second per-function development bound, solver budget, and dual
Z3/Axeyum shadow configuration. The producer reports zero unknown splits and
zero disagreements. Its fail-closed validator and Axeyum's independent
consumer accept 17,035 events, 1,225 paths, 1,081 assertions, 3,769 checks,
2,812 unique queries, 957 exact duplicate occurrences, and 1,502 model reads.
All policies reproduce 2,542 SAT and 1,227 UNSAT occurrences with no unknowns,
errors, disagreements, or original-query replay failures.

Separate capped release processes measure ratios to the Z3 time recorded on
the identical occurrence stream, including shared-arena construction for both
warm controls:

| Driver | Checks | Native Axeyum/Z3 | Exact cold | Snapshot/LCP | Per-lineage |
|---|---:|---:|---:|---:|---:|
| `win10-vwififlt` | 1,536 | 2.209x | 2.896x | **0.974x** | 1.458x |
| `sqfs-intel-DptfDevGen` | 561 | 2.679x | 2.991x | 1.225x | **0.689x** |
| `windows-update-intel-audio-IntcSST` | 1,672 | **0.426x** | 0.555x | 1.063x | **0.242x** |
| weighted bounded sum | 3,769 | 1.255x | 1.591x | 1.049x | **0.698x** |

The policy reversal is material. Snapshot is best on `vwififlt`, but loses to
Z3 on the other two drivers. Per-lineage replay is sub-Z3 on Dptf and IntcSST,
but replays 16,734 inherited roots on `vwififlt` and spends about 1.398 seconds
building child prefixes there. Across the suite it replays 26,930 fork roots.
Maximum observed process high-water RSS is 47.8 MB cold, 65.5 MB snapshot, and
106.5 MB lineage.

All 1,502 snapshot model reads remain evaluable: 1,480 reproduce the recorded
value and 22 choose a different satisfying value. Per-lineage reports 1,479
matches and 23 valid divergences. These are legitimate model non-uniqueness,
not verdict or replay failures.

The Glaurung correctness repairs are independently committed as `57c6c09`
(SAT-only model-driven choices), `d450d2a` (explicit extension-source
coercion), and `dbdc6bf` (capture-contract documentation). Focused tests cover
the non-SAT no-choice/no-assertion rule and the mismatched extension source in
both rendering and native Axeyum translation.

## Alternatives

Enabling snapshot by default from the first driver was rejected because the
same policy is 1.225x and 1.063x Z3 on the next two streams. Enabling lineage by
default from the weighted result was rejected because it is 1.458x Z3 and uses
the most memory on `vwififlt`. Selecting solely from scope depth was rejected
because driver topology and fork reconstruction dominate that counter in the
reversal. Treating the IntcSST strict-sort failures as Axeyum errors was rejected
because the producer's extension metadata was inconsistent; explicit consumer
coercion repairs the declared semantics while preserving Axeyum's strict IR.

## Consequences

Multi-driver GQ7 functionality and opportunity are now measured, but native
integration and default admission remain open. The next implementation slice is
to carry retained per-lineage state through Glaurung's actual worker/path
boundary, measure delta-only assertion and fork construction in place, and keep
the existing snapshot path available for a fixed-policy comparison. GQ9 may
only choose between them after repeated clean processes show a non-regressing
online rule with bounded memory. GQ1 still needs phase attribution at that
native boundary; GQ8 remains gated on its sound replay and invalidation design.
