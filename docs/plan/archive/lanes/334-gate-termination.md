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

**The ledger sweep is bounded at three scales.** Its build probe had no timeout
at all; its per-row timeout was `subprocess.run(shell=True, timeout=N)`, which
kills only the direct child (measured: grandchild survives at all three command
shapes); and it had no whole-sweep budget, so the summed per-row budgets came to
993,952 s — 11.5 days. Now capped, tree-killed, and deadlined at 9,900 s,
deliberately under `check.sh`'s 10,800 s cap so the informative stop wins and
unreached facts are named as `NOT RUN`.

The caps are anchored to repository measurements, not chosen: 30 min default
(the whole non-cargo half extrapolates to ~45 min), 2 h for anything that builds
(worst measured cargo step 509 s, contention documented at 4–7x), 4 h for `test`
(never timed; nearest recorded artifact is the 6,588 s workspace nextest sweep).

Probe: 8 cases / 19 assertions, ~90 s, no cargo. Mutation sweep: 7 mutants, 6
killed; the survivor is a defensive guard whose precondition is unreachable on
this host and is reported rather than excused. **The probe caught two defects in
the fix it was written to verify** — the missing group kill, and a Python reaper
that broke out of its kill loop when the direct child was reaped and so never
sent SIGKILL.

Next for whoever picks this up: the process-substitution `read`s in
`check-autogenesis-apply-search.sh` (3 sites) and
`check-autogenesis-induction-search.sh` (1) are individually unbounded and only
bounded from outside by the step cap; and `check.sh` execs itself through
`cargo-serialized.sh`, so it can wait up to 90 minutes for the slot before any
step timing begins. Both are noted in ADR-0623 and neither is fixed here.

<!-- plan-section: landed-changes -->

| 2026-08-30 | ADR-0623 | Every gate step is time-bounded, and a cap must be proved to fire. Per-step caps in `check.sh` with a third outcome; `--kill-after` plus an explicit process-group kill in both aggregate gates; the ledger sweep bounded per-row, per-tree and whole-sweep; `scripts/check-gate-step-timeout.sh` registered in `check.sh` and the justfile. |
