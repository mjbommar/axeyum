# Lane: inert-controls — the 188 Python controls no gate runs

<!-- plan-section: lane-status -->

**Triage in progress (`WIP`, inert-controls, 2026-08-27).** Starting state
measured in this worktree:

```
CONTROL_REGISTRATION|controls=20|orphans=0|py_controls=382|py_orphans=188|py_baseline=188|py=ok
```

188 of 382 `scripts/tests/test_*.py` suites are named by no caller
(`scripts/check.sh`, `justfile`, `hooks/pre-push`, `.github/workflows`). The
ratchet pins the count, so the floor is permanent and nobody chose it. Task is
the three-way split — obsolete / deliberately slow / live-but-unwired — not a
bulk registration.

<!-- plan-section: landed-changes -->

| 2026-08-27 | `pending` | Open the lane; record the starting measurement. |
