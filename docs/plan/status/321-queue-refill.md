# 321 — queue refill

<!-- plan-section: lane-status -->

## Status

IN PROGRESS (early stub commit; measurement under way).

Deficiency: `scripts/check-dispatchable-frontier.py` reports 3 dispatchable
`ml430` mirrors and exits 0. A warning nobody watches is not a gate, and the
queue has been hand-refilled four times.

Measured so far (2026-08-30, this lane):

- `python3 scripts/check-dispatchable-frontier.py` -> exit 0, DISPATCHABLE 3.
- `python3 scripts/gen-autogenesis-nursery-refill.py --check` -> exit 0,
  `entries=200 ... combined=414 attested=411 unattested=3`.
