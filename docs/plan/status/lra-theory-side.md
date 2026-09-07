# Lane: lra-theory-side — the QF_LRA theory side (final-check call count, atom-cap budget)

<!-- plan-section: lane-status -->

**`WIP`, lra-theory-side, 2026-09-07.** QF_LRA is the largest single arithmetic
gap on the board after [ADR-1732](../../research/09-decisions/adr-1732-second-reference-per-division-not-a-replacement.md)
re-measured the frontier: Yices 2.7.0 decides 181 of the committed 200-file
list, cvc5 145, ours 97. The census splits the loss two ways — **31 search
timeouts** and **23 declines at the 1,024-atom online-LRA admission cap** — with
no third class.

This lane attacks the **theory** side, not the engine. Engine unification was
measured on 2026-09-06 and is not a speed win (`CdclT` is 3.4% *faster* than the
native core on the committed benchmark). The open half of the timeout class is
the **`final_check` call count** (1,150–15,000 per file); a prior slice already
removed one redundant `O(rows × columns)` pass inside the pivot, which is the
per-call half.

Method is fixed by the last slice's finding: the plan's stated cause was false
(everyone believed the tableau needed a warm start; six counters wired in before
any change measured `simplex_cold_restarts = 0` across 6,571 checks). So:
**wire the counter, then look.** Diary, including every hypothesis that turns
out wrong: [`docs/research/12-performance/lra-theory-side-2026-09-07.md`](../../research/12-performance/lra-theory-side-2026-09-07.md).

**Next.** Baseline counters on the 33-file population
(`bench-results/adr-1701-slice-1-20260905/qf_lra_population.tsv`), then a change
justified by them. The atom cap is load-bearing (removing it was measured at 0
new decides and 54 memory aborts), so if it moves it becomes a **measured memory
budget with a number** under ADR-1752, never a raised constant.

<!-- plan-section: landed-changes -->

| 2026-09-07 | lra-theory-side | Lane opened: status file and diary with the pre-registered hypotheses, ranked before any measurement. |
