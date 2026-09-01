# Lane: nursery-draw-17 — author nursery refill draw 17 and clear the dispatchable floor

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, nursery-draw-17, 2026-09-01).** EARLY COMMIT — this
block records the baseline re-measurement only; the draw is not authored yet.

Baseline at `b558d9b5a` (this worktree == `origin/main`, clean, merge was a
no-op), each gate run bare with its exit status captured before any grep:

| gate | exit | headline |
| --- | ---: | --- |
| `gen-autogenesis-nursery-refill.py --check` | **0** | `entries=460 ... env=2829 development=170 held-out=170 train=120 screen_drift=31` |
| `check-autogenesis-holdout-isolation.py` | **0** | `held_out=186 files_scanned=1110 verdict=PASS` |
| `check-holdout-adjacency.py` | **0** | 18 held-out families, 0 refused, 4 undisclosed (advisory) |
| `check-dispatchable-frontier.py` | **1** | G7 queue-below-floor, **2** dispatchable, floor 10 |
| `validate-facts.py` | **0** | — |
| `check-autogenesis-nursery.py` | **1** | pre-existing cross-population `depends_on` component |

Two corrections to what I was briefed, both measured rather than inherited:

- The dispatchable frontier is **2**, not 3 (ADR-1420 measured 3 on `a6c531eab`).
- `gen-autogenesis-nursery-refill.py --check` is **green** at `b558d9b5a`;
  ADR-1430 recorded it red at `46bc65cc4`, and ADR-1445's membership freeze is
  what returned it to green. `screen_drift=31` is that thinning, published.

Next: the two R11 disclosure reviews, then the draw.
