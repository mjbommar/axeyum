# ADR-0192: Accept Glaurung's path-owned replay-cache default

Status: accepted
Date: 2026-07-16

## Context

ADR-0190 keeps Axeyum's generic replay-checked SAT cache disabled unless a
caller supplies explicit bounds. ADR-0191 then accepts Glaurung's path-owned
cache-off/cache-on measurement control while withholding production admission
until a clean repeated two-driver gate clears the existing correctness,
finding, performance, memory, and environment alarms.

That clean gate is now complete. The decision is downstream and scoped: it
asks whether Glaurung's already bounded adaptive warm integration should enable
the Axeyum cache for its independently owned path solvers. It does not ask to
change `IncrementalBvSolver` constructors or Axeyum's framework-level default.

## Decision

Accept Glaurung commit `e177142` as the bounded path-owned replay-cache default.

When `GLAURUNG_AXEYUM_REPLAY_SAT_CACHE` is unset, newly created Glaurung
`lineage`, `auto`, and `adaptive` path sessions enable ADR-0190's exact
replay-checked SAT cache with the accepted per-path bounds of 64 entries, 4,096
scalar model values, and 262,144 Bool/QF_BV payload bits. `off`, `false`, or
`0` select the fixed disabled control; invalid values fail closed to off.

The admission does not widen the cache boundary:

- snapshot mode, ordinary one-shot solving, and every cap fallback remain
  cache-free;
- each cache remains owned by one arena-bound incremental solver and never
  crosses a path, arena, thread, process, or artifact;
- only exact scalar SAT duplicates are retained, and every hit passes the
  existing original-term replay before reaching Glaurung;
- ordinary UNSAT, `Unknown`, errors, non-scalar or oversized models, and strict
  prefixes never become cache verdicts;
- strict prefixes continue to reuse only GQ7's retained AIG/CNF/SAT state;
- Glaurung's separate adaptive 2-to-9 live-session policy, 512-assertion cap,
  one-shot fallback, cache telemetry, terminal cleanup, and hard 4 GiB process
  gate remain mandatory; and
- Axeyum's public `IncrementalBvSolver` cache remains disabled by default. A
  generic framework default would require separate cross-client evidence.

## Evidence

The clean gate uses Glaurung `d5475f6`, Axeyum `2b6e264c`, the same clean
dual-backend release binary, three SurfacePen processes and three fixed-budget
NETwtw10 processes per policy, hard 4 GiB child limits, and otherwise identical
adaptive warm policy. Each policy executes 92,721 checks. All 185,442 combined
checks agree with Z3, every unknown split is zero, warm traffic repeats exactly,
and finding-output hashes are identical within and across policies.

Cache-on traffic repeats exactly in all three processes per driver:

- SurfacePen: 2,464 retained checks, 154 hits, 2,310 misses, 2,099 SAT
  insertions, 211 declined UNSAT results, 832 deterministic evictions, and zero
  replay failures; and
- NETwtw10: 20,380 retained checks, 2,464 hits, 17,916 misses, 13,593 SAT
  insertions, 4,323 declined UNSAT results, zero evictions, and zero replay
  failures.

Every process terminates with zero cache entries, model values, and model bits.
The higher hit counts than consecutive-exact snapshot counters demonstrate
sound recovery of non-consecutive exact queries within the same path-owned
arena, without treating prefixes as hits.

Against cache off, cache on changes:

| Driver | Axeyum time | Axeyum/Z3 ratio | Median RSS | Z3 time |
|---|---:|---:|---:|---:|
| SurfacePen | -1.16% | -0.67% | -6.88% | -0.50% |
| NETwtw10 | -2.38% | -2.08% | -1.52% | -0.30% |

All predeclared 3% Axeyum-time, 3% normalized-ratio, 5% median-RSS, and 2%
absolute-Z3-drift alarms pass. Axeyum population CV is 0.58% on cache-on
SurfacePen and 0.13% on cache-on NETwtw10. The exact committed artifacts are:

- `lineage-adaptive-cache-off-v1.json`, SHA-256
  `95eefcb669f4f1a4c22109fcef8a40c6d0fb50476747627c1f43f132b6a8f132`; and
- `lineage-adaptive-cache-on-v1.json`, SHA-256
  `9c010538b579d36e20fdc02a92af8e6f02ea43887354ca55397256a19eba74e3`.

The fail-closed comparator accepts the named off-to-on transition with its
ordinary thresholds. All 30 Glaurung Axeyum-backend tests and all 13 lineage
runner tests pass after the default change; the parser test proves unset and
explicit on select the same fixed policy while explicit/invalid off values
remain disabled.

## Consequences

GQ8 is complete for Glaurung's available measured families: exact same-arena
SAT reuse is replay-checked, bounded, telemetry-visible, non-regressing, and on
by default only at the downstream path-owned boundary. New drivers or changed
exploration topology must re-run the same gate, and the explicit off control is
retained for causal comparison and incident response.

The result does not authorize larger cache bounds. SurfacePen's 832 evictions
are compatible with a net win; capacity remains fixed until a separate
memory/performance experiment proves another bound. It also does not authorize
cached UNSAT, cross-arena models, or prefix verdicts.

The primary Glaurung performance lane now returns to fresh native attribution:
CNF remains the largest measured retained stage, followed by AIG construction
and SAT. Any GQ5 or GQ6 change still needs exact work, replay, findings, memory,
and same-stream timing gates.

## Alternatives

Keeping the downstream cache off was rejected because both held-out families
improve Axeyum time, normalized ratio, and median RSS while every semantic and
environment gate passes. Raising capacity to remove SurfacePen evictions was
rejected because the accepted 64-entry policy already wins and larger retained
state has no causal gate. Enabling the generic Axeyum default was rejected
because this evidence covers one consumer's arena/path ownership and workload,
not all incremental clients.
