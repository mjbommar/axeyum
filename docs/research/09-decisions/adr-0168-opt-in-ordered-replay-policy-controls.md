# ADR-0168: Opt-in ordered replay policy controls

Status: accepted
Date: 2026-07-15

## Context

ADR-0167 establishes sound explicit-lineage replay, but its first fork strategy
constructs every child by replaying the complete inherited prefix into a fresh
solver. On the bounded ordered Glaurung trace, 232 forks replay 7,378 roots and
spend about 813 ms before the child's later checks. That result cannot by itself
say whether lineage is better than either fresh cold solving or ADR-0164's
consecutive-snapshot longest-common-prefix policy: the three paths had not run
over identical occurrence bytes in independently measurable processes.

Memory also needs a process boundary. Running all policies sequentially would
make Linux's high-water RSS monotonically include earlier policies and would
mislabel the later mode's memory. The existing trace's `backend_nanos` cannot
serve as a Z3 baseline: Glaurung measures around its shadow `solve` call, which
runs both Z3 and Axeyum before returning Z3 authoritatively.

Glaurung remains an opt-in downstream workload and capture producer. These
controls do not add Glaurung types or lifecycle semantics to Axeyum's IR,
lowering, solver, model, proof, or checker APIs.

## Decision

Extend the independent `glaurung-ordered-trace` consumer with three separately
runnable, opt-in policies after the mandatory T2 validation:

1. `--cold-occurrences` replays every ordered occurrence from its exact
   content-addressed SMT-LIB bytes through a fresh parse, arena, and one-shot
   solver. Every SAT result retains `solve_smtlib`'s original-query replay.
2. `--snapshot` builds one shared arena and drives one retained
   `IncrementalBvSolver` from the longest common prefix of consecutive complete
   check snapshots. It does not use path lineage. Each check validates the
   exact active constraint sequence and evaluates subsequent recorded model
   reads under the returned replay-checked model.
3. `--lineage` is the ADR-0167 policy; `--warm` remains its compatibility alias.

Each mode reports occurrence/check p50 and p95 where applicable, total replay
time, outcomes, retained structural gauges, model-value divergence, policy and
timeout identity, the trace-manifest hash, and Linux process high-water RSS
before and after the selected mode. Policies are intended to run in separate
processes on the same trace. The mandatory unique-query and model-choice T2
preflight remains outside each policy's reported replay timer.

This decision accepts a diagnostic comparison surface and one bounded result.
It does not select a production default, claim a Z3 comparison, or close T4.

## Evidence

Focused tests exercise the cold and snapshot controls on the same forked trace
as the lineage test. The snapshot control retains an identical consecutive
query instead of adding another root. Both snapshot and lineage fail closed if
a checked assertion is absent from the query store. The binary passes strict
all-feature Clippy and focused tests under the 4 GiB wrapper.

Three separate release processes replayed the same bounded
`win10-vwififlt.sys` artifact: 3,309 events, 235 paths, and 784 checks. Every
policy decided 473 SAT / 311 UNSAT with zero verdict disagreements and the
mandatory T2 preflight remained green.

| Policy | Timed replay | p50 / p95 occurrence | Process high-water RSS after | Model reads |
|---|---:|---:|---:|---:|
| fresh cold occurrence | 2.737 s | 3.925 / 4.927 ms | 29.7 MB | T2 choices checked separately |
| consecutive snapshot/LCP | 0.545 s | 0.593 / 1.515 ms | 38.4 MB | 241 match / 2 valid divergences / 0 unevaluable |
| explicit lineage, fresh fork-prefix replay | 1.371 s | check-only 0.353 / 0.847 ms | 83.9 MB | 242 match / 1 valid divergence / 0 unevaluable |

Snapshot replay retains 24,364 roots across occurrence transitions, adds 671,
pops 640, and sees 126 unchanged consecutive snapshots. Its peak retained
structure is 14,442 AIG nodes, 15,113 CNF variables, and 50,199 clauses. The
lineage policy retains as many as 20 live paths and peaks at 109,056 AIG nodes,
109,573 variables, and 143,041 clauses while replaying 7,378 fork-prefix roots.

On this single development run, snapshot replay is about 5.0x faster than the
cold occurrence control and 2.5x faster than naive lineage replay. This selects
snapshot reuse as the implementation to repeat and harden; it is not a stable
ratio or production-policy claim.

## Alternatives

Running the three policies in one process was rejected because process
high-water RSS would not be attributable by mode. Treating query-store dedup as
the cold control was rejected because it erases 276 real occurrences. Treating
`backend_nanos` as Z3 time was rejected because it includes both shadow
backends. Making lineage the default because it has explicit ownership was
rejected because explicit ownership does not compensate for its measured fork
construction cost.

## Consequences

T4 now has identical-occurrence cold, snapshot, and lineage controls with
original-query replay and separately runnable memory measurements. The bounded
evidence says that the current client stream's consecutive ordering already
captures more useful reuse at much lower state cost than cloning every lineage
by prefix replay.

GQ7 remains open. Repeat the three controls across clean processes and more
drivers, capture exact bytes for every assertion, and add per-backend Z3 and
Axeyum timings at the producer boundary. Only then compute warm-versus-Z3
break-even and decide whether snapshot state, a cheaper sound fork mechanism,
or a hybrid ownership policy should become an integration recommendation.
