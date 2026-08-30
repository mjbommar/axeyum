# Lane: gate-termination — the full gate has to be able to finish

<!-- plan-section: lane-status -->

**WIP** (gate-termination, 2026-08-30). `scripts/check.sh` had **zero**
timeout-guarded steps, so one hung step hung the whole aggregate gate forever. A
live run was reaped after **nine hours** — 0% CPU at every level of the process
tree, reparented to init, log last written 68 minutes in and stopped mid
`=== facts-replay ===`.

First measured finding, before any fix: `scripts/check-fact-evidence-replay.sh`
does **not** use `timeout(1)` at all. Its 21 mentions of "timeout" are
`subprocess.run(..., timeout=N)`, and that only kills the direct child. Probed
here (`scripts/tests/test-gate-step-timeout.sh` carries the pinned form):

| checker shape | Python `TimeoutExpired` fires | grandchild survives |
| --- | --- | --- |
| `cmd` | yes, 2.00s | **yes (1 orphan)** |
| `cmd \| cat` | yes, 2.00s | **yes (1 orphan)** |
| `cmd & wait` | yes, 2.00s | **yes (1 orphan)** |

So a timed-out checker leaves its `cargo` running. Cargo's build-directory lock
has no timeout, so the orphan blocks every later cargo checker in the same
sweep — which is the shape of a gate that never returns rather than one that
runs slowly.

<!-- plan-section: landed-changes -->
