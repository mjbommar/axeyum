# Lane: ax-cache — the canonical constraint cache (ADR-0303's key) as a library feature of the warm engine (item 8, 2026-09-16 list)

<!-- plan-section: lane-status -->

**AX-CACHE (`landed`, ax-cache, 2026-09-17).** `IncrementalBvSolver` owns a
`CanonicalConstraintCache` keyed by the sorted, duplicate-elided set of live
assertion identities (stack plus assumptions; order, frame shape and repeats
do not matter), behind `SolverConfig::canonical_constraint_cache` /
`AXEYUM_CANONICAL_CACHE` (registered, OFF as shipped). Exact `sat` is served
only after the cached model replays against the live set; `unsat` for the same
set or any superset; a cached model of a subset when it replays; `unknown`
never cached; deterministic 4,096-entry LRU. Two mutation controls each kill
exactly one test (the subset soundness-negative; the shipped default).
Replaying the DptfDevGen owner-1 session: 589 of 1,206 checks (48.8 %) served
from the cache, verdict digest byte-identical on and off, 0 disagreements, 0
replay failures, wall 1.19–1.31 s → 0.77–0.83 s. `QF_BV` pinned-list A/B as
the regression control (see ADR-2144). Python `Config`/`Incremental`/
`IncrementalStats` carry it. ADR-2144. **Next:** Glaurung consumes it for its
path-owned warm solver (item 5 on its list) and re-runs ADR-0303's mode matrix
with the library cache as the `exact`/`structural` arms; a cross-solver
variant needs a structural term hash in `axeyum-ir` and a name-keyed model.

<!-- plan-section: landed-changes -->

| 2026-09-17 | ax-cache | `CanonicalConstraintCache` in `incremental.rs` (exact / superset-unsat / replay-guarded model reuse, deterministic LRU), `SolverConfig::canonical_constraint_cache` + `AXEYUM_CANONICAL_CACHE` (config registry), `stats()` cache counters, Python `Config`/`Incremental`/`IncrementalStats` surface with stubs, `tests/canonical_constraint_cache_2144.rs` (13 tests, pre-push, two mutation controls), `warm_session_age --canonical-cache` + verdict digest, the DptfDevGen replay and the `QF_BV` A/B (`bench-results/canonical-cache-20260917/`), sizing note, ADR-2144. |
