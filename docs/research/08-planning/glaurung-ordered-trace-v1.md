# Glaurung ordered warm-trace v1 handoff

Status: proposed producer/consumer contract
Date: 2026-07-14

## Purpose

The existing Glaurung capture is the correct GQ1/GQ10 cold artifact: exact
SMT-LIB bytes are content-addressed, trusted Z3 verdicts are indexed, and the
Axeyum manifest assigns stable families and tiers. It deliberately cannot
answer GQ7/GQ8 questions because content deduplication erases repeated checks,
path-prefix relationships, scope operations, worker ownership, and model values
that steer exploration.

Warm integration needs a separate event trace. This note defines the smallest
v1 handoff that can replay the explorer's real solver interaction without
turning capture into a second solver API. It does not authorize changes in the
Glaurung repository; it is the contract Axeyum needs from a producer-side
implementation.

## Findings from the current capture seam

The reviewed `GLAURUNG_DUMP_QUERIES` hook writes each decided query as
`<sha256>.smt2` and appends `<sha256>\t<verdict>` to `index.tsv`. The companion
builder classifies the text and selects a deterministic representative tier.
That establishes query identity, but the warm trace must correct five losses:

1. A repeated query is one content file, so occurrence count and order vanish.
2. The complete active assertion set is dumped, so push/pop deltas and shared
   prefixes cannot be reconstructed reliably from text comparison.
3. Only decided queries are indexed; `unknown`, timeout, and operational-error
   events must remain visible in a functionality trace.
4. The index append is not a cross-process transaction. The regenerated pack
   found 23 duplicate rows, and strict ingestion isolated 2,225 ill-sorted
   scripts; validate before publishing an event and merge per-process output
   atomically.
5. A SAT verdict does not describe which model values Glaurung consumed to
   choose its next path. Arbitrary valid models may differ between backends,
   so those reads must be explicit rather than mislabeled as verdict
   disagreement.

Content-addressed SMT-LIB remains useful. The trace references those bytes; it
does not duplicate a full script at every occurrence.

## Deliverable layout

An access-controlled trace directory contains:

```text
trace-manifest-v1.json
events-v1.ndjson
queries/
  <sha256>.smt2
query-index-v1.json
```

`queries/` is a deduplicated byte store. `events-v1.ndjson` is never
deduplicated: one line is one observed interaction. Producers write a unique
per-process temporary trace and publish by atomic rename; a deterministic
finalizer validates and merges traces. It must never have multiple processes
append an uncoordinated shared index.

The manifest binds schema version, Glaurung revision and dirty state, driver
paths plus content hashes, analysis command/configuration, solver feature and
trusted oracle version, toolchain, host identity, worker count, start/end time,
event/query-index SHA-256, and access classification. Query-index rows retain
the existing path/content-hash/verdict/family facts where applicable.

## Event envelope

Every NDJSON line has these fields:

| Field | Contract |
|---|---|
| `version` | Integer `1` |
| `event_seq` | Unique contiguous trace-wide serialization integer assigned by the finalizer |
| `event` | One of the event variants below |
| `analysis_id` | Stable ID for one driver-analysis invocation |
| `process_id` | Stable producer-process ID within the analysis |
| `process_seq` | Contiguous observation order within that producer process |
| `worker_id` | Stable solver/explorer worker within the analysis |
| `worker_seq` | Contiguous per-worker integer |
| `path_id` | Stable logical explorer path/state ID |
| `path_seq` | Contiguous event order within that path |
| `location` | Optional stable program/driver location ID, not an unstable pointer |
| `monotonic_ns` | Diagnostic timestamp relative to analysis start; never used as semantic order |

`event_seq` records deterministic final serialization; it is not evidence of a
semantic total order between concurrent producer processes. `process_seq`
preserves each process's observations, while replay correctness uses explicit
lineage plus worker/path sequences. Cross-process transfers need an explicit
`path_transfer` edge. IDs are opaque strings or integers whose allocation
policy and finalizer merge order are recorded in the manifest.

## Event variants

- `analysis_start` / `analysis_end`: driver identity and terminal status.
- `path_start`: `parent_path_id` (null only for a root), fork reason, and the
  inherited `scope_digest`.
- `path_end`: exhausted, pruned, finding, error, or deadline reason.
- `push`: new stable `scope_id` and prior depth.
- `assert`: `scope_id`, stable `constraint_id`, exact assertion-byte hash or
  query-store reference, sort-validation status, and semantic role
  (`path-condition`, `branch`, `memory`, `concretization`, or `other`).
- `check`: stable `check_id`, check purpose, scope depth, active constraint
  count and ordered `scope_digest`, exact full-query content hash, outcome
  (`sat`, `unsat`, `unknown`, or `error`), classified unknown/error detail,
  backend timing, and resource counters.
- `model_read`: `check_id`, stable symbol/expression ID, sort/width, returned
  value, and whether the value affected exploration. Reads are ordered and
  occur only after a SAT check.
- `model_choice`: the ordered model reads used for one branch/concretization,
  chosen value(s), policy ID/version, and downstream path ID(s).
- `pop`: `scope_id`, prior/resulting depth, and resulting `scope_digest`.
- `path_transfer`: optional explicit fork/migration/merge record. A merge must
  name every parent and its assertion-state digest; absence means v1 does not
  claim merge support.

`constraint_id` identifies semantic assertion bytes and may repeat. The event
identity remains `(analysis_id, event_seq)`. `scope_digest` is a versioned hash
over the ordered active `(scope_id, constraint_id)` stack. The replayer rebuilds
it from events and compares it at every `check`, `path_start`, and `pop`; a
digest is an integrity check, not a substitute for the event history.

## Controlled model-choice boundary

Backend models may assign unconstrained bits differently while both satisfy the
same query. The integration gate therefore separates three facts:

1. verdict agreement;
2. each model's replay against the exact active query; and
3. downstream choice agreement under a named Glaurung policy.

Every value that affects exploration must emit `model_read` plus
`model_choice`. On shadow replay, constrain or validate the recorded chosen
values against each backend. If both admit the choice, replay the same path. If
only one admits it, record `model-choice-divergence`; do not call it a solver
verdict disagreement or silently let the executions drift. A future
deterministic minimization/enumeration policy is a versioned producer decision,
not assumed by this schema.

## Producer validation

The finalizer fails closed unless:

- final event serialization and process/worker/path sequences are unique and
  contiguous within their declared domains;
- path lineage references earlier starts and every path has one terminal event;
- scope depth never underflows, scope IDs match, and terminal stacks follow the
  declared lifecycle policy;
- every assertion and full-query reference exists, hashes exactly, parses as
  strict QF_BV, and is well sorted before its event is admitted;
- reconstructed active assertions hash to every check's query bytes and
  `scope_digest`;
- each model read follows SAT and has the declared sort/width; constraining the
  recorded values consumed by a choice must leave the exact query SAT (the
  trace need not pretend those reads form a complete backend model);
- check outcomes include unknown/error events rather than dropping them;
- query-index duplicates have identical bytes and verdicts, with conflicts
  fatal; and
- manifests, event bytes, query membership, and source/tool identities are
  complete before atomic publication.

## Axeyum replay and acceptance

The implementation sequence is dependency ordered:

1. **T0 — repair producer publication.** Use explicit `coerce_to`-equivalent
   width handling, strict pre-index sort validation, per-process output, and an
   atomic conflict-checking merge for the cold and trace stores.
2. **T1 — emit a small ordered trace.** Capture at least one root/fork,
   repeated check, nested push/pop, SAT model read that drives exploration,
   UNSAT prune, and unknown/error if naturally present. Validate it with the
   rules above before scaling.
3. **T2 — add an Axeyum trace validator/replayer.** First reconstruct every
   cold query from events and match content hash/verdict. Report duplicate,
   prefix-extension, delta-assertion, scope-depth, and model-choice rates.
4. **T3 — wire real warm solving.** Keep one arena/translator and
   `IncrementalBvSolver` per retained worker/path state; map events to
   push/assert/check/pop, assert only the delta, and preserve original-query
   replay. Fork behavior must be explicit: clone supported state, replay a
   validated prefix, or decline—never share mutable solver state accidentally.
5. **T4 — measure and optimize delta entry.** Report p50/p95 check latency,
   total solver time, fixed per-check overhead, peak memory, learned/CNF reuse,
   and the depth where warm Axeyum beats cold v3 and Z3. Only then change
   `assert_configured` to process newly added/affected terms.
6. **T5 — consider caching/policy.** Exact-query caching is admitted only if
   trace duplicate frequency justifies it. Prefixes use retained sound state,
   not cached verdicts. GQ9 auto policy follows held-out cold and ordered-trace
   validation.

Exit for GQ7 is same-stream shadow replay with 100% classified events, zero
verdict disagreements, zero original-query replay failures, explicit
model-choice divergences, deterministic resource bounds, and a measured warm
break-even. The synthetic 7.5x result and the deduplicated 13,462-query pack do
not satisfy that exit criterion.

## 2026-07-15 snapshot bridge result

ADR-0164 lands a sound pre-lineage bridge in Glaurung commits `016935d` and
`b09ec6b`. With `GLAURUNG_AXEYUM_WARM_REUSE` set, one adapter per explorer
thread translates each complete assertion snapshot into a retained Axeyum
arena, compares structurally interned assertion roots, pops the divergent
suffix, and asserts only the new suffix. Numeric Glaurung expression IDs are
never compared across cloned pools. This implements real retained
arena/AIG/CNF/SAT reuse through the current one-shot trait; it does not invent
path or scope lineage that the producer has not supplied.

Three alternating `win10-vwififlt.sys` shadow pairs preserve 13,126/13,126
agreements, zero unknown splits, zero warm resets, and identical findings.
Median Axeyum time falls 17.784 to 9.426 seconds (-47.0%), and the median paired
Axeyum/Z3 ratio falls 2.648x to 1.462x. Each warm run observes 5,609 consecutive
exact snapshots, retains 679,870 prefix roots, adds 8,027 roots, and pops 8,026.

This advances T3 but does not satisfy its exit. T1/T2's versioned trace remains
required to validate worker/path ownership, non-consecutive forks, explicit
push/pop events, model reads/choices, unknown/error classification, memory,
per-check latency, and true per-lineage break-even. Keep the bridge opt-in until
that trace and multi-driver repetitions support a GQ9 production policy.
