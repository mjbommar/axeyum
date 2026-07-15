# ADR-0164: Opt-in Glaurung snapshot-to-incremental reuse

Status: accepted
Date: 2026-07-15

## Context

GQ7 identifies retained warm state as the remaining structural route below the
cold-path plateau. The full ordered warm-trace v1 contract still requires
worker/path lineage, explicit scopes, and exploration-driving model reads, but
Glaurung's current solver seam already exposes an ordered stream of complete
assertion snapshots. Waiting for the full producer contract would leave a
large, directly testable prefix-reuse opportunity unmeasured.

Glaurung clones `ExprPool` at a path fork. Prefix expression IDs remain stable,
but each sibling may append a different expression at the same numeric ID.
Therefore a process-global cache keyed by Glaurung `ExprId` would be unsound.
The adapter must establish identity after structural translation.

## Decision

Accept Glaurung commits `016935d` and `b09ec6b` as an opt-in GQ7 bridge. Keep
one Axeyum `TermArena` and `IncrementalBvSolver` per explorer thread, translate
each complete snapshot into the retained structurally interned arena, compute
the longest common prefix of Axeyum `TermId` assertion roots, pop the divergent
suffix, and assert only the new suffix. Each new root receives its own selector
scope so any later structural prefix can be restored exactly.

Select the bridge only when `GLAURUNG_AXEYUM_WARM_REUSE` is set. The production
wrapper uses the raw assertion policy; the concrete adapter also exposes an
explicit delta-preprocessing constructor for controlled experiments. Retain
ordinary one-shot behavior as the default until multi-driver and lineage gates
establish a non-regressing production policy.

Reset the complete retained session after any push, assertion, or check
operational error. Preserve `unknown` as a normal result. Export process-wide
counts of checks, consecutive exact snapshots, structurally retained prefix
roots, added roots, popped roots, and error resets. This is retained-state
reuse, not verdict caching: every check still invokes Axeyum and every SAT
candidate still passes original-term replay.

## Evidence

Focused Glaurung tests cover raw and delta-preprocessed modes, exact snapshot
reuse, extending/shrinking snapshots, empty snapshots, and divergent sibling
pools whose different new expressions deliberately share the same numeric
`ExprId`. The sibling test proves that reuse follows translated structure: one
branch is SAT with `x = 5`, while its colliding sibling is UNSAT. Both focused
tests pass. The dual `solver-z3,solver-axeyum` `ioctlance` build passes with the
documented GCC include path needed by this host's `z3-sys` bindgen.

Three alternating release pairs run the Z3-authoritative
`win10-vwififlt.sys` stream. Every process executes 13,126 identical checks,
reports 13,126 agreements, zero disagreements, zero unknown splits, the same
finding counts, and zero retained-session resets.

| Policy | Median Axeyum | Median Z3 | Median paired Axeyum/Z3 |
|---|---:|---:|---:|
| ordinary one-shot | 17.784 s | 6.741 s | 2.648x |
| opt-in snapshot reuse | 9.426 s | 6.446 s | 1.462x |

Median Axeyum time improves 47.0%, and the median paired ratio improves 44.8%.
Every warm run reports the same deterministic reuse structure: 5,609
consecutive exact snapshots, 679,870 retained prefix roots, 8,027 added roots,
and 8,026 popped roots. Thus 98.83% of the 687,897 encountered assertion-root
occurrences are retained rather than reasserted after translation. The
remaining 1.462x ratio and run-to-run host variance prevent a parity claim.

## Alternatives

Waiting for the complete ordered trace before exercising any retained state was
rejected because complete snapshots provide a sound structural-prefix seam and
the measured opportunity is large. Treating raw Glaurung `ExprId` as a global
identity was rejected because cloned siblings reuse IDs for different nodes.
Cloning a solver into every path state was rejected because
`IncrementalBvSolver` deliberately owns non-clone retained SAT state. Exact
verdict caching was not added: it needs the separate GQ8 replay, capacity,
versioning, and lineage contract. Default enablement was rejected because the
current evidence covers one driver and consecutive process order, not the
multi-driver/worker/path distribution required by GQ9.

## Consequences

GQ7 now has a real end-to-end retained arena/AIG/CNF/SAT path and a measured
same-stream win through Glaurung's existing one-shot trait. The full trait
redesign is no longer a prerequisite for initial warm measurement.

GQ7 is not complete. The bridge infers only consecutive structural prefixes;
it cannot name worker/path lineage, reconstruct non-consecutive fork state,
classify scope/model-choice divergence, or establish per-path break-even. The
next gate is the ordered trace v1 producer plus multi-driver repetitions. Use
that artifact to compare snapshot-LCP reuse with explicit per-lineage state,
measure memory and p50/p95 latency, and decide GQ9 default admission. GQ8
verdict reuse remains separately trace- and replay-gated.
