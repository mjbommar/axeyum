# ADR-0160: Opt-in incremental client phase attribution

Status: accepted
Date: 2026-07-15

## Context

GQ1 requires an exact explanation for the gap between `axeyum-bench` and
Glaurung's native `IncrementalBvSolver` entry path. Existing cold artifacts
attribute the standalone one-shot backend, but cannot see Glaurung arena
creation, `ExprPool` translation/interning, fresh incremental construction,
client model extraction, caller overhead, or ordered duplicate occurrences.
Comparing unrelated aggregate timers was therefore insufficient to choose
between GQ5 incremental encoding work, GQ7 retained warm state, and a separate
cold client API.

Always-on timers would tax the production path being measured. A single output
file shared by processes would also make query order and duplicate accounting
ambiguous, while a normalized/deduplicated capture cannot recover the extending
client stream.

## Decision

Add explicit `IncrementalBvSolver::with_config_and_profiling` construction and
a monotone `IncrementalBvStats` snapshot. The opt-in path records:

- configured word canonicalization, term-to-AIG lowering, incremental CNF
  extension, SAT search, model lift, and original-root replay durations;
- successful root encodings and attempted scalar-BV checks; and
- current retained AIG node and CNF variable/clause gauges.

`delta_since` isolates one query or retained segment with saturating component
deltas. Ordinary constructors retain zero durations/counters and perform no
profiling clock reads; structural gauges remain observable. Profiling does not
select preprocessing, demand slicing, or any other solver policy.

Glaurung's diagnostic adapter keys every record by SHA-256 of the exact SMT-LIB
bytes produced by its existing capture renderer, but excludes rendering/hash
and JSON output from native phase time. It preserves the current raw assertion
policy, times client-only phases separately, records one monotone process-local
sequence, and writes one JSONL file per process. Operational output failure is
an error rather than silently dropping evidence. The environment switch must
be set before the process's first native check.

Accept `scripts/summarize-glaurung-native-profile.py` as the fail-closed reader
for schema v1. It rejects malformed/incomplete/out-of-order records, impossible
phase totals, root/check mismatches, mixed policies/timeouts, and outcome
disagreement on hashes overlapping a supplied capture manifest. It preserves
occurrences and reports unique/duplicate counts, p50/p95 latency, phase shares,
structure totals, and family overlap. A separate switch requires 100% decided.

## Evidence

The Axeyum profile tests cover snapshots/deltas, configured batch rewriting,
SAT/UNSAT replay, structural gauges, and the zero-counter ordinary constructor.
The Glaurung backend's 16 focused tests include exact capture-hash identity,
phase/structure completeness, model extraction, serialization, and
process-isolated output. All-feature Axeyum solver Clippy and strict rustdoc are
green under the 4 GiB wrapper.

An exploratory release run at Axeyum `c8ffb43d` and Glaurung `f201448`, on
`win10-vwififlt.sys`, preserves Z3-authoritative exploration and executes
13,126 identical shadow queries. All 13,126 decide and agree; neither backend
returns unknown. The ordered stream contains 7,065 unique hashes and 6,061
duplicate occurrences. Fifty-two unique hashes (154 occurrences) overlap the
pinned representative manifest with no verdict conflict.

The validated native profile attributes 17.429 seconds:

| Phase | Time | Share |
|---|---:|---:|
| bit blast | 7.461 s | 42.81% |
| incremental CNF encode | 6.550 s | 37.58% |
| SAT | 1.260 s | 7.23% |
| translation/interning | 0.789 s | 4.53% |
| model lift + replay | 0.320 s | 1.84% |
| all other named + unattributed | 1.050 s | 6.02% |

Latency is 0.881 ms p50 and 3.667 ms p95. The phase profile totals 38.26
million AIG nodes and 66.94 million incremental clauses across occurrences.
The same Z3-authoritative stream without diagnostics measures 18.826 seconds
in the ordinary Axeyum wrapper versus 6.478 seconds in Z3 (2.906x). The
profiled wrapper measures 24.415 seconds because it also renders, hashes, and
writes every diagnostic record; those costs are deliberately excluded from
the 17.429-second phase total. These are single-driver exploratory numbers, not
a replacement for the clean multi-driver GQ10 gate.

All 52 exact overlapping hashes preserve AIG size between Glaurung translation
and the current standalone raw artifact. Weighted across their 154 occurrences,
both paths build 494,150 AIG nodes, while incremental Glaurung emits 875,083
clauses versus the one-shot encoder's 506,480 (+72.78%); native structure is
stable across repeat occurrences. This confirms that Glaurung's `ExprId`
sharing survives into the AIG and strengthens ADR-0156's measured incremental
gate-fusion diagnosis. The next clean gate must regenerate the benchmark at the
same revision before attaching timing significance to this structural pairing.

## Alternatives

- **Use only the shadow wrapper's aggregate timer.** Rejected: it cannot
  separate translation, lowering, encoding, search, replay, or diagnostic I/O.
- **Enable timers for every solver.** Rejected: production users should not pay
  clock reads and counter updates for diagnostics they did not request.
- **Profile only deduplicated SMT-LIB.** Rejected: it loses first-use effects,
  occurrence weight, and the duplicate/prefix evidence needed by GQ7/GQ8.
- **Treat client and benchmark AIG differences as assumed.** Rejected: exact
  query-hash pairing makes sharing survival and clause inflation measurable.
- **Optimize SAT next.** Rejected by this evidence: lowering plus CNF owns
  80.39% while SAT owns 7.23%.

## Consequences

GQ1's native client boundary is now instrumented and one real ordered driver is
attributed. The result chooses GQ5 incremental gate fusion as the next bounded
cold implementation target: same AIG, excess incremental clauses. In parallel,
the 46.18% duplicate-occurrence rate makes the already-defined GQ7 ordered
trace and retained per-worker/path state a high-value structural route; exact
verdict caching remains behind sound scope/prefix measurement.

Do not enable either GQ4 implementation or prioritize GQ6 from this result.
Next, run the schema on a clean multi-driver process set, pair every overlapping
hash with a same-revision raw benchmark artifact, retain order, and then design
one clause-fusion slice against the measured incremental gate mix.
