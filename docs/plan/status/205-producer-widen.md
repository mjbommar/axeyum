# Lane: producer-widen — widen the conclusion-directed producer to a second family

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, producer-widen, 2026-08-28).** Widening
`producers::conclusion_directed_application` (landed by lane 198 against
`nat.modeq`) to a **second** family of currently-OPEN facts, so that
`facts_via_multi_target` rises on targets that were open at lane start.

Baseline at lane start, measured:

- `check-autogenesis-holdout-isolation.py`: `held_out=37|files_scanned=1101|settled=0|references=0|verdict=PASS`
- `fact-frontier.py`: 125 open entries; `ready_count=92`, `no-route=6`,
  `proof-route-only` unmatched 77.

Family selection in progress. This block will be replaced with the measured
outcome before the lane closes.

<!-- plan-section: landed-changes -->

| 2026-08-28 | producer-widen | lane opened; baseline holdout isolation PASS, frontier 125 open |
