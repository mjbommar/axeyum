# Lane: solver-cycle-regression — dependency-cycle regression in `axeyum-solver`

<!-- plan-section: lane-status -->

**Fixed and committed** (`WIP`, solver-cycle-regression, 2026-08-29).

## What the gate actually said (correcting the task text)

The exact FAIL text this task was handed — `NEW CYCLE MEMBERS: grp, x`,
`LARGEST CYCLE GREW: 0 -> 3 lines (from nothing)`, `LARGEST CYCLE GREW:
2 -> 802 lines (401.00x)` — is **not from `scripts/analyze_solver_module_graph.py
--check`**, the gate `check.sh` actually runs (`scripts/check.sh:711`). It is
stdout from `scripts/tests/test_analyze_solver_group_collapse.py`'s own
mutation-control fixtures: `grp`/`x` are literal synthetic module names that
test file constructs on purpose to prove the guard fires on a deliberately-bad
grouping. Confirmed by running that suite directly: **14/14 tests pass**, and
the "401x" figure is also independently a *documented historical example* in
`analyze_solver_module_graph.py`'s own source comments (a 2026-08-17 measurement
on a proposed `arith/` directory, never landed). Neither is a live regression.

The real gate, run directly (`python3 scripts/analyze_solver_module_graph.py
--check`), reported different names and different numbers throughout this
investigation — see below.

## When and why (the real regression)

`docs/refactor-2026-08/solver-module-graph-baseline.json` was last written by
commit `90ef09a80` on **2026-08-17 09:32:14 -0400**. The gate has been red
since **~11:27 that same day** — 12 days as of this writing, unrelated to any
lean-kernel work from today. Two commits landed in the intervening two hours,
each independently closing a previously-acyclic module into the 26-module
theory-core cycle:

Detail moved to [`../notes/280-solver-cycle-regression.md`](../notes/280-solver-cycle-regression.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | `0348564ab` | Break the `auto<->nat_induction` and `qinst_egraph<->quant_instance_set_cert` cycle-closing edges from 2026-08-17; `modules_in_cycles` now matches the pre-regression baseline exactly. Residual mass/fan-out growth on the same gate is pre-existing, tracked by D1/D3, left untouched. |
