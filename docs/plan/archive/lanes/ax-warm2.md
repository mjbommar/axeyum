# Lane: ax-warm2 — the linear residual after ADR-2142: keep the surviving scopes' trail across `pop`/`check` (ADR-2145)

<!-- plan-section: lane-status -->

**AX-WARM2 (`landed`, ax-warm2, 2026-09-17).** Sized at head on the
replayed DptfDevGen session (1,206 checks): `propagate` 40.6 %, the order-heap
drain after a from-scratch propagation 29.3 %, the `assignment_is_model`
self-check 8.3 %, `reset_search_state` 2.8 % — assignment re-derivation is
~76 % of the session; the retained database grows to 63k variables / 148k
clauses and the per-check trail to 40k entries. The warm core now backtracks
to the longest common prefix of the previous and next assumption sequences
(CaDiCaL `ilb=1`) instead of unwinding, registers clauses added in between
against the live assignment through a re-init list (z3's
`m_clauses_to_reinit`), and takes the reset when under half the trail would
survive; invariant: the assignment at every kept level equals a fresh
propagation of the surviving clauses. Replayed session 1.21 → 0.45 s at three
interleaved rounds per arm, same verdict+model digest, propagations per check
20,976 → 2,107 (July's BatSat engine: 0.87 s); synthetic stream at parity.
Pinned lists on s7 (200 `QF_BV` + 200 `QF_ABV`, 24 s, interleaved): 0 verdict
movers, 0 flips, 0 `:status` disagreements; of the time movers rerun 3×/arm,
`QF_ABV` 9 stably faster / 1 stably slower. Shipped ON
(`DEFAULT_WARM_KEEP_TRAIL = true`, `AXEYUM_WARM_KEEP_TRAIL=off` is the old
schedule), ADR-2145 `accepted`. A new session fuzz for the incremental path
(`tests/incremental_bv_session_fuzz.rs`: push/assert/check/pop against a fresh
one-shot, a replay, and z3 driven through the same stream) caught the first
cut's wrong-`unsat` and is in the pre-push hook; two mutation suites, 10
guards, 10 killed. **Next:** a Glaurung re-pin and six-cell rerun (not run
here); the `assignment_is_model` pass over every clause per `sat` is the
largest remaining linear term and could be made incremental.

<!-- plan-section: landed-changes -->

| 2026-09-17 | ax-warm2 | ADR-2145: `Cdcl::add_input_clause_live` / `reinit_replay` / `resume_search_state`, `NativeIncrementalCdcl::set_keep_trail` with the longest-common-prefix resume and `KEEP_TRAIL_MIN_REUSE_SHARE`, `SolverConfig::warm_keep_trail` (`AXEYUM_WARM_KEEP_TRAIL`, default ON), trail/reuse/counter gauges through the three layers, `warm_session_age` band columns, `tests/incremental_bv_session_fuzz.rs` (pre-push), `keep_trail_*` unit tests, mutation suites `warm-keep-trail-2145*`, `bench-results/warm-keep-trail-20260917/`. |
