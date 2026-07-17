# Glaurung ordered warm-trace v1 handoff

Status: T1/T2 accepted in ADR-0166; opt-in T3 per-lineage replay accepted in
ADR-0167; T4 controls accepted in ADR-0168 and complete one-driver capture in
ADR-0169, multi-driver/native-integration publication open; T5 open
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
# Optional production-topology extension:
native-assertions/
  <pack-sha256>.json
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
- `warm_owner_share` / `warm_owner_release`: optional production-topology
  events on the analysis path. They record one source owner and the exact
  serial sibling reference expansion/release order; they never imply parallel
  mutable solver sharing.

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

## 2026-07-15 T1/T2 result

Glaurung commits `7a11c29` and `32cabb0` implement the opt-in producer and its
external fail-closed validator. Axeyum's independent consumer is:

```sh
cargo run --release -p axeyum-bench --bin glaurung-ordered-trace -- \
  TRACE_DIR --timeout-ms 1000 --out axeyum-replay-v1.json
```

Add `--warm` to run ADR-0167's explicit per-lineage retained solver replay
after the independent T2 checks.

The consumer does not trust producer validation. It verifies artifact hashes,
reconstructs lineage and scope state, strictly parses every unique QF_BV query,
re-solves each query with original-assertion model replay, reconciles all
occurrences/outcomes, and independently checks the satisfiability of every
unique exploration-driving expression/value constraint.

ADR-0166 records the bounded real acceptance result: 3,309 events, 235 paths,
784 checks, and 508 unique queries, all decided with no recorded disagreement;
243 model choices reduce to 158 unique exact constraints and all remain SAT.
The stream contains 276 duplicate occurrences (35.2%), 271 prefix extensions,
and maximum scope depth 45. This establishes the functionality and reuse
opportunity needed for T3. It is not a clean multi-driver publication, warm
performance result, or reason to make reuse automatic.

## 2026-07-15 T3 result

ADR-0167 adds opt-in ordered warm replay without importing Glaurung into the
solver architecture. One shared parsed arena supplies stable term identity;
each live path owns a distinct `IncrementalBvSolver`. A fork must match its
parent's active constraint sequence and then replays that validated prefix into
a fresh child solver. No mutable SAT state is shared or cloned.

The bounded development trace remains 784/784 verdict-agreed (473 SAT, 311
UNSAT), with original-assertion replay on every warm SAT candidate. All 243
model reads evaluate: 242 match the recorded exploration value and one exposes
a legitimate alternative-model choice. The current producer stores exact
assertion bytes only through checked queries; 13 assertions on never-checked
terminal branches therefore remain explicitly unmaterialized. A check or
inheriting checked fork that reaches one fails closed.

The initial strategy creates 232 fork solvers and replays 7,378 inherited
roots. That prefix replay costs about 813 ms of the 1.249 s warm pass; check
latency is about 0.322/0.672 ms p50/p95. Peak live structural gauges are 20
paths, 109,056 AIG nodes, and 143,041 clauses. These single-run development
numbers select T4 work; they are not a warm-vs-cold, memory, multi-driver, or
default-policy claim. Next run cold occurrence and ADR-0164 snapshot controls
on identical bytes, capture every asserted term, add peak RSS/resource identity,
and establish the actual break-even before considering GQ8/GQ9.

## 2026-07-15 T4 policy-control result

ADR-0168 adds independently runnable controls after the mandatory T2 checks:

```sh
cargo run --release -p axeyum-bench --bin glaurung-ordered-trace -- \
  TRACE_DIR --timeout-ms 1000 --cold-occurrences --out cold.json
cargo run --release -p axeyum-bench --bin glaurung-ordered-trace -- \
  TRACE_DIR --timeout-ms 1000 --snapshot --out snapshot.json
cargo run --release -p axeyum-bench --bin glaurung-ordered-trace -- \
  TRACE_DIR --timeout-ms 1000 --lineage --out lineage.json
```

The cold control solves every ordered occurrence from its exact SMT-LIB bytes
with a fresh parse/arena/solver. The snapshot control reconstructs consecutive
complete assertion sets over one shared arena and maps their longest common
prefix to one retained solver. The lineage control remains ADR-0167's distinct
solver per path with validated prefix replay at forks. Run each in a separate
process so Linux high-water RSS remains attributable.

On the same bounded trace, all three policies agree on all 784 checks (473 SAT,
311 UNSAT) with mandatory original-query replay. Cold takes 2.737 s, snapshot
0.545 s, and naive lineage 1.371 s. Snapshot occurrence latency is 0.593/1.515
ms p50/p95 and process high-water RSS is 38.4 MB, versus 83.9 MB for lineage.
Snapshot adds only 671 roots while retaining 24,364 across transitions; lineage
replays 7,378 roots into 232 fresh fork solvers. Model choices remain explicit:
snapshot observes 241 recorded-value matches and two valid divergences;
lineage observes 242 and one, with zero unevaluable reads.

This bounded result selects consecutive snapshot reuse for repetition and
hardening, not a default. The trace's `backend_nanos` surrounds Glaurung's
combined shadow call and therefore includes both Z3 and Axeyum; it is not a Z3
timer. T4 remains open pending producer-side per-backend timing, complete
assertion bytes, repeated clean multi-driver processes, and a real
warm-versus-Z3 break-even.

## 2026-07-15 complete-capture result

ADR-0169 closes the two one-driver capture gaps. Glaurung now persists every
distinct assertion line, including never-checked terminal roots, and each
assert event supplies sorted free-symbol declarations. Every check separately
records same-occurrence Z3 and Axeyum time. The external validator and Axeyum
consumer both fail closed on byte, membership, declaration, or timing drift;
older v1 artifacts remain readable but report the absent fields honestly.

The clean Glaurung `497b1c6` sample contains 3,280 events, 235 paths, 503 unique
queries, all 180 assertions, 776 checks, and 241 model reads. The independent
consumer decides all 776 occurrences (470 SAT, 306 UNSAT) under all three
policies. Explicit lineage now reports zero unmaterialized assertions and zero
unmaterialized fork-prefix roots.

Recorded native Glaurung time is 0.808 seconds for Z3 and 2.095 seconds for
Axeyum (2.593x). The exact-byte cold consumer takes 2.631 seconds. Snapshot
replay plus its 13.5 ms shared-arena build takes 0.476 seconds (0.590x recorded
Z3), whereas naive lineage plus build takes 1.291 seconds (1.598x Z3). Snapshot
p50/p95 occurrence latency is 0.548/1.179 ms and high-water RSS is 38.1 MB;
lineage replays 7,378 fork roots and reaches 88.7 MB.

This establishes bounded same-stream structural headroom below Z3 and explains
the real native client bar without claiming integration parity: the snapshot
control is an independent replayer and does not include Glaurung translation.
Scope-depth telemetry is now executable: a repeated process is faster than Z3
in 45/46 observed depth buckets, with only the two-check depth-12 bucket slower;
all observed depths from 13 onward are faster. Treat that threshold as
descriptive, not causal. Repeat cleanly across drivers and carry the selected
retained-snapshot policy through the actual client boundary before a default or
user-visible performance claim.

## 2026-07-16 exact timeout-continuation replay contract

ADR-0210 extends the independent consumer for ADR-0209's fixed-occurrence gate.
Validation and measurement use separate budgets: `--timeout-ms` remains the
mandatory strict unique-query and model-choice validation budget, while
`--policy-timeout-ms` applies only to the requested retained replay. Run the
control and candidate in separate processes over the same published trace:

```sh
cargo run --release -p axeyum-bench --bin glaurung-ordered-trace -- \
  TRACE_DIR --timeout-ms 5000 --lineage --policy-timeout-ms 250 \
  --out lineage-timeout-control.json
cargo run --release -p axeyum-bench --bin glaurung-ordered-trace -- \
  TRACE_DIR --timeout-ms 5000 --lineage --policy-timeout-ms 250 \
  --continue-on-unknown --out lineage-timeout-candidate.json
```

An explicit policy budget permits classified policy nondecisions to be
reported rather than aborting the independent validation. It never permits an
opposite SAT/UNSAT verdict, and a recorded or initial replay error remains
fatal. The candidate performs exactly one additional `check`
on the same retained solver after the first returns `Unknown`; a repeated
`Unknown` or continuation error preserves the first result. The JSON partitions
attempts into SAT/UNSAT recoveries, repeated unknowns, and errors and records
initial/continuation time separately. Both summaries bind the trace-manifest
hash, event hash, replay-executable hash, validation budget, policy budget,
policy outcome counts, original-model replay, retained structure, and process
high-water RSS.

Full tcpip traces make query-payload ownership part of the correctness and
resource contract. Sequential fixed-size worker batches validate each content
hash, parse, and strictly solve that exact byte buffer once; worker exit returns
one-shot solver allocations to the OS. The parent retains only the file path,
fixed-size assertion-sequence identity, outcomes, and fixed-size ordered
occurrence identity. Snapshot and lineage replay reconstruct active scopes from
the already validated push/assert/pop stream; they do not retain a duplicate
constraint vector for every check, fork, and path end. Query/model-choice reads
revalidate their content hash on demand. This keeps the independent validator
inside the 4 GiB process envelope without sampling or weakening exact-order,
field, count, scope, or verdict checks.

The producer must preserve expression-DAG sharing in those payloads. Glaurung
renders each non-leaf once through deterministic nested SMT-LIB `let` bindings;
binding names are postorder ordinals, not pool-local expression IDs. Therefore
alpha-equivalent DAGs built in pools with shifted internal IDs retain identical
bytes and content hashes. A recursive tree renderer can expand one shared DAG
to gigabytes, while raw expression-ID binders keep formulas small but destroy
cross-pool content identity; both forms are rejected by producer regressions.

The authoritative Glaurung `3c3c77e` tcpip trace now closes this independent
mechanism gate. Under 4 GiB it records 301,852 events, 15,501 paths, 70,823
exact checks, 50,429 unique queries, 9,860 assertions, and 27,731 model reads;
the producer validator and both Axeyum replays accept the complete stream. The
no-continuation lineage control observes 13 policy `Unknown`s. The candidate
observes 14 initial `Unknown`s, then one same-instance retry recovers 7 (one SAT
and six UNSAT), repeats 7, and errors 0. It has zero decided disagreements,
zero unevaluable model reads, zero unmaterialized assertions/fork roots, and
identical event/query/model/retained-structure identity. Warm replay changes
188.646 to 192.356 seconds (+1.97%) and external maximum RSS changes 1,262,596
to 1,263,024 KiB (+0.034%), inside the existing alarms. ADR-0210 therefore
accepts the bounded mechanism while leaving native Glaurung admission open.

This is a causal fixed-stream mechanism experiment. Snapshot and naive-lineage
replay do not reproduce Glaurung's current adaptive source-owner/serial-lease
topology, so a replay win alone cannot change the downstream default. Native
admission still requires the production topology and the established exact
traffic/finding, time, ratio, RSS, reset, replay, and repeated-variance gates.

## 2026-07-17 native production-topology extension

The additive `glaurung-native-ordered-replay-v1` manifest block supplies the
facts intentionally absent from the public text replay. Every assert event may
reference a deterministic, topologically ordered native expression-DAG pack by
its own content hash. The independently rendered SMT assertion hash remains
the cross-tool identity: a native consumer must re-render the imported pack
and reject it unless the bytes hash to that exact constraint ID. Multiple
native shapes may therefore bind the same public assertion without collapsing
client translation work.

Every check in this extension has a `warm_replay` object containing the source
owner ID, requested retain depth, persistent/temporary partition, source-prefix
digest, and live synchronization result. Owner-share/release events reconstruct
the serial DFS lease. The producer validator requires exact native-store
membership, topological child references, valid partitions/digests, balanced
leases, and manifest totals. Axeyum's independent public consumer deliberately
does not trust or import the native packs, but it accepts the additive events
only after independently validating their scope/lease structure; its strict
SMT parse, verdict, original-model, and model-choice checks remain unchanged.

Glaurung's separate `ordered_native_replay` executable is the T5 client-boundary
consumer. Built without Z3, it reconstructs the native typed pool, shared
source-prefix identity, adaptive direct-delta sessions, serial leases, bounded
fallbacks, and replay-checked SAT cache, then drives every occurrence through
the same `solve_for_path_delta` entry as live exploration. Fresh control and
one-continuation processes bind the identical trace/event hashes, canonical
finding hash, and independent Axeyum replay hash. Opposite decided verdicts,
solver errors, synchronization drift, resets, cache replay failures, or
nonzero terminal gauges are fatal; honest `Unknown` results remain explicit.
The fixed 156-function repeated time/RSS gate is pending and therefore no
native default changes in this note.
