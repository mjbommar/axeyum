# Lane: gate-termination — the full gate has to be able to finish

<!-- plan-section: lane-status -->

**The aggregate gate is time-bounded, and the bound is proved to fire**
(`landed`, gate-termination, 2026-08-30). `scripts/check.sh` had **zero**
timeout-guarded steps of 401, so one hung step hung the gate forever — a live
run was reaped after **nine hours**, 0% CPU at every level, reparented to init,
log stopped mid `=== facts-replay ===`. Every step now carries a generous
per-step cap and a third outcome, `TIMED OUT` = UNCHECKED, which is counted and
named separately from a failure and can never read as a pass (ADR-0623).

**The second finding was worse than the first.** `scripts/check-fast.sh` had a
per-step cap from the day it was written and it did not bind: `timeout N` sends
SIGTERM and then waits **forever** while still exiting 124, so a caller testing
for 124 sees a correct-looking verdict after an arbitrarily long wait. A run of
it was found stuck 23 minutes on a step with a 3-second budget. A cap nobody has
watched bite is a cap you do not have — which is why the deliverable is a probe,
`scripts/check-gate-step-timeout.sh`, registered in both aggregate gates. It is
the time analogue of `cargo-serialized.sh --self-check`.

**`--kill-after` is necessary and not sufficient**, and the probe is what found
that. `timeout` signals the child it monitors, not the tree beneath it, and
`trap '' TERM` sets SIG_IGN which is inherited across exec. Measured at a 2s cap
with an uncapped positive control, in two fixture shapes:

| | sleeper last | sleeper backgrounded |
| --- | --- | --- |
| uncapped (control) | 1 | 1 |
| `timeout -k` | 1 | 1 |
| `timeout -k`, group kill omitted | 1 | 1 |
| `timeout -k` + `kill -KILL -$pgid` | **0** | **0** |

That surviving grandchild IS the nine-hour bug: an orphaned `cargo` holds the
build-directory lock, whose wait is unbounded, so every later cargo step blocks
on a process nothing will reap. 4,064 of the ledger's 4,122 `checker_command`s
invoke cargo.

Detail moved to [`../notes/334-gate-termination.md`](../notes/334-gate-termination.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | ADR-0623 | Every gate step is time-bounded, and a cap must be proved to fire. Per-step caps in `check.sh` with a third outcome; `--kill-after` plus an explicit process-group kill in both aggregate gates; the ledger sweep bounded per-row, per-tree and whole-sweep; `scripts/check-gate-step-timeout.sh` registered in `check.sh` and the justfile. |
