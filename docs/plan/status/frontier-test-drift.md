# Lane: frontier-test-drift — fix the 10 pre-existing failures in `scripts/tests/test_fact_frontier.py`

<!-- plan-section: lane-status -->

**IN PROGRESS, frontier-test-drift, 2026-09-01.** Picking up the "found, not
fixed" item from `docs/plan/status/frontier-holdout-screen.md`: 10 failures
in `python3 scripts/tests/test_fact_frontier.py`, diagnosed there as (1) the
`contract()` fixture missing the `sizing` key ADR-1510 made required, and (2)
two facts used as hard-coded open test targets
(`F:ml430-int-add-modeq-right-e58108ee`,
`F:ml430-int-add-modeq-left-ee732b5b`) having since been `proved`.

Starting point: worktree was branched from an older `main` (47 commits
behind, missing ADR-1510 itself); merged local `main` (fast-forward-clean, no
conflicts) before reproducing, so the fix lands against current `main`
(`5d03dd4f6` at merge time).

Reproducing per-test causes now; fixture and drifted-target fixes to follow
this stub.

<!-- plan-section: landed-changes -->

| 2026-09-01 | (pending) | status(frontier-test-drift): open the lane stub |
