# 351 — nursery draw 6b

<!-- plan-section: lane-status -->

**IN PROGRESS — this is an early stub committed before any measurement is
complete, per the lane's commit-early rule. Nothing below is a result yet.**

Task: author nursery draw 6, now unblocked by `Nat.dist` and `Nat.nth`
landing on `main`. ADR-0645 declined the draw when zero held-out-safe
families existed; it named these two constants as the exact unblock.

Baseline measured at merge-base `635ff3952`:
`python3 scripts/check-dispatchable-frontier.py` exits **1**,
`FAIL: G7 queue-below-floor: 6 dispatchable mirror(s), floor 10`.
