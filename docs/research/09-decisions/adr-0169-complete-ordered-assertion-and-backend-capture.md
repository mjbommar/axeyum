# ADR-0169: Complete ordered assertion and backend capture

Status: accepted
Date: 2026-07-15

## Context

ADR-0168's first identical-occurrence controls exposed two producer gaps. The
trace persisted exact query scripts only after a check, so 13 assertions on
terminal never-checked branches had hashes but no bytes. It also recorded one
`backend_nanos` value around Glaurung's shadow wrapper. That wrapper executes
both Z3 and Axeyum, making the value unusable as either backend's baseline.

Persisting the missing assertion lines alone was insufficient. A terminal
assertion can reference a free symbol that never appears in any checked query.
Axeyum correctly rejected the first complete-store experiment at shared parse
with `unknown identifier sym22_8`; reconstructing a declaration from the name
without producer evidence would weaken the untrusted-artifact boundary.

Glaurung is an opt-in capture producer and downstream workload. The trace
schema remains outside Axeyum's product IR and solver APIs.

## Decision

Extend Glaurung ordered trace v1 additively:

1. persist every distinct exact assertion line as
   `assertions/<sha256>.smt2`, including roots on branches that never check;
2. bind each assert event to its canonical relative path and carry sorted
   producer-derived free-symbol names and widths;
3. record the distinct assertion count in the manifest;
4. record `z3_nanos` and `axeyum_nanos` separately on every check, while
   retaining `backend_nanos` as the total shadow-wrapper time; and
5. make the producer validator fail on assertion-store membership/hash/symbol
   drift and inconsistent per-backend timing.

The solver wrapper publishes the last call's timing through worker-local state,
which the trace reads immediately after `solve`. Ordinary solving behavior and
return values are unchanged. A missing backend is represented by `null`.

Axeyum's independent consumer remains backward compatible with older v1
artifacts that have neither extension. When `assertion_count` is present it
requires the complete store, exact event membership, and consistent symbol
declarations. It builds the shared arena from producer-declared symbols rather
than guessing. It also aggregates the two per-backend timers and rejects a sum
that exceeds the recorded total. Snapshot control output includes deterministic
scope-depth buckets with check count, Axeyum occurrence time, recorded Z3 time,
and ratio, plus an observed monotone threshold. The threshold is descriptive
for one trace, not a formula-size cost model.

## Evidence

Glaurung's focused dual-backend producer test emits and externally validates a
fixture with two complete assertion blobs and three separated check timings.
The dual-backend library check passes under the 4 GiB wrapper; existing
repository warnings are unchanged. Glaurung commits `73a2bac`, `de7d259`, and
`497b1c6` implement complete bytes/timing, ignore machine-local Claude settings
so source identity can be clean, and add assertion symbol declarations.

Axeyum's focused five-test consumer suite and strict all-feature Clippy pass.
It continues to accept the older 3,309-event trace and honestly reports zero
per-backend timed checks. On the new clean Glaurung `497b1c6` trace it validates
3,280 events, 235 paths, 503 unique queries, all 180 distinct assertions, 776
checks, and 241 model reads. All three Axeyum policies agree on 470 SAT / 306
UNSAT with original-query replay, and lineage reports zero unmaterialized
assertions or fork-prefix roots.

One separate-process release round measures:

| Boundary | Time | Ratio to recorded Z3 |
|---|---:|---:|
| recorded native Glaurung Z3 | 0.808 s | 1.000x |
| recorded native Glaurung Axeyum | 2.095 s | 2.593x |
| exact-byte cold Axeyum consumer | 2.631 s | 3.257x |
| snapshot replay + shared-arena build | 0.476 s | 0.590x |
| explicit lineage replay + shared-arena build | 1.291 s | 1.598x |

Snapshot replay adds 665 roots, pops 634, and retains 24,117 across occurrence
transitions. Its p50/p95 occurrence latency is 0.548/1.179 ms and process
high-water RSS is 38.1 MB. Naive lineage again replays 7,378 roots, takes about
827 ms in fork construction, and reaches 88.7 MB. Snapshot model reads are 239
recorded-value matches / two valid divergences / zero unevaluable; lineage is
240 / one / zero.

A repeated snapshot process reports a 0.589x ratio to recorded Z3 including the
shared-arena build. Snapshot occurrence time is below Z3 in 45 of 46 observed
scope-depth buckets. Depth 12 is the only slower bucket and contains two
checks; every observed bucket at depth 13 or greater is faster, so the
machine-readable monotone observed threshold is 13. This is not evidence that
depth alone causes break-even, and the sparse exception reinforces the need for
multi-driver repetition.

This is one clean bounded driver run. Snapshot's sub-Z3 replay ratio is real for
the independent same-occurrence control, but it excludes Glaurung's native
translation/integration work and is not a production backend claim.

## Alternatives

Reconstructing free-symbol declarations from `sym<ID>_<width>` names was
rejected because artifact checking must consume producer evidence rather than
guess it. Storing complete standalone SMT-LIB scripts per assertion was
rejected because declarations would be duplicated heavily and the assertion's
existing byte hash would no longer identify the stored file. Treating aggregate
shadow atomics as per-occurrence timing was rejected because interleaved workers
would lose call identity.

## Consequences

The current ordered capture can now replay every traced assertion and compare
against the actual same-stream native Z3 and Axeyum backend timers. The bounded
result reconciles the reported real-client gap: native Axeyum is 2.59x Z3 on
this stream, while the retained snapshot control has structural headroom below
Z3 if integrated without reintroducing client overhead.

T4 is functionally complete for one clean driver but not published across the
driver set. Repeat clean processes and drivers, then integrate the selected
snapshot policy through Glaurung's client boundary. GQ8 caching and GQ9
automatic activation remain downstream of that multi-driver and
native-integration gate.
