# Lane: ax-warm2 — the linear residual after ADR-2142: keep the surviving scopes' trail across `pop`/`check` (ADR-2145)

<!-- plan-section: lane-status -->

**AX-WARM2 (`in-progress`, ax-warm2, 2026-09-17).** Sizing at head
(`e7d132705`, DptfDevGen r1 owner 1 replay, 1,206 checks, cores 0-7):
p90 per band 0.31 → 8.5 ms, total 1.97 s at load 11 (1.20 s at load 5).
`perf` shares: `propagate` 40.6 %, `heap_percolate_down` 29.3 % (the order
heap drained by `pick_branch` after a from-scratch propagation assigns every
retained variable), `IncrementalSat::solve_inner` 8.3 % (the
`assignment_is_model` self-check over all 148k clauses), `run`/`search_loop`
3.8 %, `reset_search_state` 2.8 %, `assert_root` 2.0 %. So assignment
re-derivation (propagate + heap drain + reset + assumption install) is
~76 % of the session; everything else ~24 %. Retained database by band:
5.4k vars / 10.7k clauses at check 50, 32k / 72k at 500, 63k / 148k at
1,206; the trail after a check grows 1.5k → 34k → 40k entries. The change:
`AXEYUM_WARM_KEEP_TRAIL` (OFF by default) makes the warm core backtrack to
the longest common prefix of the previous and next assumption sequences
(CaDiCaL `ilb=1`) instead of unwinding, and registers clauses added in
between against the live assignment (`Cdcl::add_input_clause_live`). First
measurement, same digest `9fe6d1e14afe9c19`, same 19 conflicts: total
1.195 → 0.809 s, last-band p50 1.29 → 0.36 ms, p90 5.28 → 4.42 ms; the p90
checks are the sibling-branch checks that pop one scope and push a new one,
whose cone (~15k of 47k trail entries) no reuse can keep. **Next:** unit and
differential controls, the pinned-list A/B, ADR-2145.

<!-- plan-section: landed-changes -->

| 2026-09-17 | ax-warm2 | `Cdcl::add_input_clause_live` / `resume_search_state`, `NativeIncrementalCdcl::set_keep_trail` and the trail gauges, `SolverConfig::warm_keep_trail` (`AXEYUM_WARM_KEEP_TRAIL`), `warm_session_age` band columns for clauses/vars/trail/reused. |
