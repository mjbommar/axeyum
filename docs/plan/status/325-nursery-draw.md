# 325 — nursery draw

<!-- plan-section: lane-status -->

## Status

IN PROGRESS. Early commit, work incomplete.

Measured on arrival, against the handoff in `321-queue-refill.md`:

- `check-dispatchable-frontier.py`: **exit 0, DISPATCHABLE 23**, floor 10,
  `queue_below_floor: false`. The handoff's "RED at 3" is stale — the
  ADR-0542 amendment lane (`6f4b1e62b`, `137451362`) landed after it was
  written and returned open siblings of two spent held-out families to the
  dispatchable set.
- `check-autogenesis-holdout-isolation.py`:
  `held_out=96|files_scanned=1106|settled=0|references=0|verdict=PASS`.

Next: run the proposer, decide the draw size against the drain rate.
