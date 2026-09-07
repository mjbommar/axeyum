# Lane: bench-boolean-core — Boolean-core benchmarks and the per-conflict throughput gap

<!-- plan-section: lane-status -->

**`WIP`, bench-boolean-core, 2026-09-07.** Explaining the measured ~1.5x
per-conflict throughput gap between the native proof-producing CDCL core
(`crates/axeyum-cnf/src/proof_sat.rs`) and Kissat, and closing the
instrumentation gap the
[search-stats note](../../research/11-design-review/2026-09-05-native-core-vs-kissat-search-stats.md)
named as its own "what this does not establish": *no decision, propagation or
restart counter exists in `ProofSearchProgress`*, so the native core's own time
breakdown has never been measured. That note calls adding them "a natural next
step for a lane that owns that crate" — this lane.

Also in scope: criterion coverage for the uncovered evidence-path routines
(DRAT checking, LRAT elaboration forward/backward, binary vs text DRAT) and the
cost DRAT logging imposes on the search itself.

Running diary:
[`docs/research/12-performance/bench-boolean-core-2026-09-07.md`](../../research/12-performance/bench-boolean-core-2026-09-07.md).

<!-- plan-section: landed-changes -->

| 2026-09-07 | `pending` | Lane opened: diary with pre-registered expectations, status file. |
