# ADR-0167: Opt-in ordered per-lineage warm replay

Status: accepted
Date: 2026-07-15

## Context

ADR-0164 proves that a Glaurung adapter can retain Axeyum arena, AIG, CNF, and
SAT state across consecutive complete assertion snapshots. ADR-0166 then
accepts an untrusted ordered trace with explicit path parentage, scopes, checks,
and exploration-driving model reads. The next GQ7 boundary is to consume that
lineage rather than infer only the longest common prefix between consecutive
snapshots.

`IncrementalBvSolver` intentionally owns mutable, non-cloneable SAT state. A
fork therefore cannot copy or alias a parent's solver accidentally. The trace
also records an assertion's content hash at `assert`, while exact term bytes are
stored only as part of a query that reaches `check`; a branch that terminates
before checking can consequently have no materializable term in the query
store.

Glaurung remains an opt-in downstream workload source. No Glaurung type,
lifecycle, or policy enters Axeyum's IR or solver crates.

## Decision

Extend the independent `glaurung-ordered-trace` benchmark consumer with an
explicit `--warm` mode. After the existing T2 identity, cold-query, and
model-choice checks pass, the mode:

1. constructs one deterministic shared Axeyum arena from the exact declaration
   and assertion bytes in the content-addressed query store;
2. retains one `IncrementalBvSolver` per live trace path and maps ordered
   `push`/`assert`/`pop`/`check` events to that path only;
3. validates a fork's inherited constraint sequence against the live parent,
   then creates a fresh child solver and replays that prefix—mutable solver
   state is never shared or cloned;
4. rejects a check unless its reconstructed active scope sequence is exact,
   its solver depth agrees, and every active assertion has materialized bytes;
5. uses `IncrementalBvSolver`'s original-assertion replay before accepting each
   SAT result and requires every warm verdict to match the recorded occurrence;
6. evaluates every recorded expression/value equality against the warm SAT
   model, reporting matches, legitimate alternative-model divergences, and
   unevaluable reads separately; and
7. reports per-check p50/p95 latency, phase time, fork-prefix replay work, live
   path/retained-structure peaks, and event-only unmaterialized assertions.

An unmaterialized assertion may remain dormant through a path end. If it or an
inheriting descendant reaches a check, replay fails closed. This permits honest
classification of the current trace without inventing term bytes from a hash.

Warm replay remains opt-in. This decision accepts a functionality and
measurement boundary, not a production policy or the GQ7 performance exit.

## Evidence

Four focused tests cover choice assertion construction, scope-digest identity,
valid fork-prefix replay with independent solvers, and rejection of a check
whose active constraint is absent from the query store. The binary passes
strict all-target/all-feature Clippy and its focused test target under the 4 GiB
cap.

On the bounded ADR-0166 `win10-vwififlt.sys` development trace, warm replay
classifies all 3,309 events, creates 235 path states, and agrees on all 784
checks: 473 SAT and 311 UNSAT. Every SAT candidate passes original-assertion
replay. All 243 model reads evaluate; 242 select the recorded value and one
selects a different valid value. T2 independently proves the recorded value's
constraint satisfiable, so that divergence is explicit exploration-policy
evidence rather than a verdict disagreement.

The initial fork strategy creates 232 child solvers and replays 7,378 inherited
roots. Fork replay consumes about 813 ms of the 1.249 s warm pass. Check latency
is about 0.322 ms p50 and 0.672 ms p95. The pass observes 13 assertions whose
bytes never enter the query store; all remain dormant, and zero unmaterialized
roots reach a forked prefix or check. Peak live state is 20 paths, 109,056 AIG
nodes, 109,573 CNF variables, and 143,041 clauses. These are single-run
structural/timing diagnostics from a development capture, not a reproducible
memory or Axeyum/Z3 comparison.

## Alternatives

Cloning `IncrementalBvSolver` was rejected because its retained SAT state is
deliberately non-cloneable and accidental copies would obscure ownership and
learned-state semantics. Sharing one mutable solver among siblings was rejected
because interleaved path events would require unsound or implicit rollback.
Ignoring event lineage and continuing snapshot-LCP inference was rejected
because it cannot validate non-consecutive forks. Treating a model-value
divergence as a solver error was rejected because QF_BV models are often
non-unique; the sound requirement is that both the warm model and the recorded
choice replay against the original query.

## Consequences

T3 now has an executable per-lineage retained-state path with explicit fork
ownership, exact scope checks, original-query replay, model-choice divergence
telemetry, and bounded structural counters. It establishes where the naive
fork strategy spends time: replaying inherited prefixes, not the shared parse.

GQ7 remains open. Next compare this path with ADR-0164 snapshot inference and a
cold occurrence-by-occurrence control on identical trace bytes; add actual peak
RSS and deterministic resource identity; capture exact bytes for every asserted
constraint (including never-checked branches); and repeat cleanly across the
driver set. Only those T4 results can select a lower-cost fork strategy,
establish warm break-even, or support GQ8/GQ9 policy work.
