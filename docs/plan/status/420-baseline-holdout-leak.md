# Lane: baseline-holdout-leak — digest held-out endpoints out of the partition-edge baseline

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, baseline-holdout-leak, 2026-09-02).** ADR-1550's
`partition-edge-baseline-v1.json` wrote six crossing edges' held-out endpoint
as a plain-text fact id, so `check-autogenesis-holdout-isolation.py` is red on
main (`references=6`). Fixing the baseline format: a held-out endpoint is
stored as a salted SHA-256 digest with `held_out_endpoint: true`; the
`--baseline` comparison digests the live id before matching. Also narrowing
two gates' `artifacts/autogenesis/nursery*.json` glob, which is unanswerable
against an unrelated file matching that pattern.

<!-- plan-section: landed-changes -->

| 2026-09-02 | baseline-holdout-leak | starting: status stub only so far |
