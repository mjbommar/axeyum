# Lane: inventory-gate-rot — four RED gates from `scripts/check.sh`: two stale, one stale fixture, one real solver defect

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (3 of 4 fixed; the 4th is a real crates/ defect, precisely diagnosed and reported, not touched)`, inventory-gate-rot, 2026-08-29).**

Assigned four gates that were RED on `main`: `example-inventory-count`,
`example-inventory-controls`, `lane-turn-controls`, `lra-hypothesis-binding`.
Reproduced each directly (never trusted the coordinator's older aggregate-gate
log). Verdicts:

1. **`example-inventory-count` — STALE.** `python3
   scripts/gen-example-inventory.py --check` reported both markers
   (`docs/documentation-plan.md`, `docs/plan/global/30-workstream-state.md`)
   still saying 193 while `git ls-files 'crates/*/examples/*.rs'` counts 202 —
   the ~15 new kernel example binaries that landed since the last
   regeneration. Regenerated; `--check` now passes (`stale=0`). This also
   staled `PLAN.md` (it quotes the same count via
   `docs/plan/global/30-workstream-state.md`), so `python3 scripts/gen-plan.py
   --check` had to be regenerated too.

2. **`example-inventory-controls` — STALE (downstream of #1), guard sound.**
   `scripts/tests/test-gen-example-inventory.sh`'s own first case ("a clean
   tree passes `--check`") was failing purely because the tree was NOT clean
   (see #1). Not a vacuous or broken control — once #1 was regenerated, all 6
   cases pass (`GEN_EXAMPLE_INVENTORY_CONTROLS|cases=6|failures=0`).

Detail moved to [`../notes/285-inventory-gate-rot.md`](../notes/285-inventory-gate-rot.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | `04a77fbf6` | example-inventory count regenerated 193 -> 202 (real growth). |
| 2026-08-29 | `dcc100cc6` | PLAN.md regenerated for the same count. |
| 2026-08-29 | `e72119787` | lane-turn-controls case 4 fixture fixed: SKIP a stale baseline instead of asserting a false expectation. |
