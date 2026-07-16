# ADR-0171: Native path-owned warm reuse

Status: accepted
Date: 2026-07-15

## Context

ADR-0170 compared exact cold, consecutive-snapshot, and explicit-lineage
replay outside Glaurung's live solver call boundary. Its weighted result favored
lineage, but `vwififlt` favored snapshot and the lineage control rebuilt every
child prefix. That evidence selected native path ownership as the next bounded
experiment; it did not show what the real client would pay.

Glaurung now carries an explicit explorer path identifier through ordinary
solver calls. In opt-in lineage mode, each live path owns an independent
`SnapshotIncrementalAxeyumSolver`, including its own term arena, AIG/CNF state,
SAT state, and assertion prefix. A child never shares mutable solver state with
its parent or sibling. Its first check materializes the full inherited prefix;
later checks assert only the snapshot delta. Terminal paths close their
sessions, restarts close the old owner and allocate a new one, and calls without
an explicit path context fall back to one-shot solving rather than guessing.

This is downstream integration evidence for Axeyum's general incremental
solver interface. Glaurung remains an opt-in, untrusted workload and does not
define Axeyum's formal-reasoning architecture or default policy.

## Decision

Accept native path-owned warm reuse as the leading opt-in GQ7 integration path:

1. retain explicit per-path ownership and fail-closed one-shot fallback;
2. retain consecutive snapshot mode as a fixed diagnostic comparator, not the
   recommended policy for the measured native streams;
3. do not enable either mode by default in Axeyum or Glaurung yet;
4. require a deterministic live-session/memory budget and telemetry-visible
   eviction or fallback contract before GQ9 can auto-select lineage reuse;
5. preserve complete original-query model replay and independent sibling state
   as mandatory acceptance conditions; and
6. keep GQ8 verdict/CNF caching downstream of the ownership, invalidation, and
   replay contract.

The next GQ7 slice is lifecycle hardening, not another cold-path optimization:
bound retained sessions and inherited-prefix materialization, add phase
attribution inside the native lineage path, and test a conservative online
fallback against fixed snapshot, lineage, and one-shot policies. A default
requires wider-driver evidence and must be non-regressing in correctness,
latency, and memory.

## Evidence

The native bridge and its ownership tests are Glaurung commits `b9febbd` and
`950cca4`. The release example was built with both Z3 and Axeyum. Three
alternating rounds used a 30-second exploration deadline, a 20,000-check
budget, a 60-second solve bound, and Z3-authoritative shadow execution on the
same three real drivers used by ADR-0170. No process hit its deadline.

Each policy executed 6,986 checks per round and 20,958 checks across the three
rounds. All 41,916 combined policy/check occurrences agreed with Z3, with zero
confident disagreements, zero unknown splits, zero warm resets, and stable
query counts and findings. The table reports medians of the three paired
processes; each ratio is Axeyum time divided by the same-process Z3 time.

| Driver | Checks/round | Snapshot Ax/Z3 | Lineage Ax/Z3 | Snapshot RSS | Lineage RSS |
|---|---:|---:|---:|---:|---:|
| `win10-vwififlt` | 4,753 | 2.658x | 1.072x | 101,368 KiB | 132,820 KiB |
| `sqfs-intel-DptfDevGen` | 561 | 1.358x | 0.587x | 73,148 KiB | 77,772 KiB |
| `windows-update-intel-audio-IntcSST` | 1,672 | 1.161x | 0.172x | 114,148 KiB | 132,220 KiB |
| weighted bounded sum | 6,986 | 2.093x | **0.746x** | — | — |

The weighted snapshot Axeyum total has a 16.063-second median and 0.78%
coefficient of variation. Native lineage has a 5.537-second median and 0.28%
coefficient of variation, a 65.5% reduction and 2.90x improvement over
snapshot. Its weighted Axeyum/Z3 ratio has 0.36% coefficient of variation.

Lineage creates and closes 2,103 path sessions per round and reaches only 11
simultaneously live sessions on the two larger drivers and five on Dptf. It
retains more inherited state, however: median RSS rises 31.0% on `vwififlt`,
6.3% on Dptf, and 15.8% on IntcSST. The largest observed lineage high-water
mark is 141,124 KiB, versus 114,252 KiB for snapshot. That cost is bounded in
this experiment but is not yet governed by a public resource policy.

The native result also explains part of ADR-0170's policy reversal. The live
lineage owner reuses later checks on a path instead of reconstructing every
occurrence in an external replay process. Snapshot still performs only 4,509,
492, and 1,620 added-root operations per round on the three drivers, but its
single consecutive owner repeatedly pops across unrelated paths. Lineage adds
77,890, 2,738, and 7,848 roots while preserving each path's retained state;
that ownership is substantially faster on all three native streams.

## Alternatives

Enabling lineage by default was rejected because its retained-state memory is
higher on every measured driver and no eviction/fallback contract exists.
Keeping snapshot as the leading policy was rejected because it loses on every
native driver and is 2.093x Z3 in the weighted repeated gate. Sharing a mutable
solver between siblings was rejected because push/pop and learned-state
ownership would be ambiguous. Keying state from inferred expression identity
was rejected because client-local IDs are not a cross-path ownership proof.
Treating the external replay result as the native result was rejected because
the two boundaries have materially different prefix construction and lifetime
costs.

## Consequences

GQ7 native functionality and repeated performance evidence are now complete
for this bounded three-driver tier. GQ9 remains open: lineage is the measured
fast fixed policy, but it needs deterministic session/memory bounds, online
fallback reasons, wider drivers, and fixed-policy comparison before default
admission. GQ1 must now profile the 5.537-second native lineage total to
separate translation, first-prefix materialization, delta assertion, model
lifting, and SAT work. GQ8 remains gated on a versioned content/config/scope
identity and mandatory evidence replay.
