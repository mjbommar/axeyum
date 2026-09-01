# Lane: nursery-draw-author — author the nursery refill draw that clears the frontier floor

<!-- plan-section: lane-status -->

Status: IN PROGRESS (2026-09-01). Re-measurement done; screening and draw
authoring in flight.

## Step 1 — re-measure (done)

The worktree started **13 commits behind local `main`** and its copy of
`gen-autogenesis-nursery-refill.py` still carried the four-element
`HELD_OUT_CONSTRUCTIONS = {Nat.log, Nat.clog, Nat.log2, Nat.sqrt}`. Measured on
that stale tree the proposer reported 3 ready families with `Mathlib.Data.Nat.Log`
at **37** — a number that would have been wrong in the direction that overstates
headroom. Merged `main` (a6c531eab) and re-ran.

On the merged tree:

```
python3 scripts/propose-nursery-refill.py --remeasure          exit 0
  pinned inventory   9729 records, 4285e551680abf3b…
  screened out       7673
        5173  not-statable-here
        1699  hygienic-or-generated
         662  already-drawn
         125  divergence-registry
          14  held-out-construction
  survivors          2056 across 85 module(s)
  READY FAMILIES     2
        17  Mathlib.Data.Nat.Log
        15  Mathlib.NumberTheory.FactorisationProperties
```

`artifacts/autogenesis/refill-headroom-v1.json` regenerates with a **zero diff**
against what `main` committed, so the re-measurement reproduces ADR-1405 exactly
and nothing has moved under the concurrent divergence-registry lane.

```
python3 scripts/check-dispatchable-frontier.py                 exit 1
  FAIL: G7 queue-below-floor: 3 dispatchable mirror(s), floor 10
  open ml430 mirrors: 211
    held-out (blind evaluation):        185
    mutation negative controls:          12
    structurally blocked by divergence:  11
    DISPATCHABLE:                         3
```

Both family counts match the brief's figures (17 / 15). `dispatchable_yield(2)
= 10·(2 − ⌈2/3⌉) = 10`, exactly the floor with no slack.

## What remains

Screening both families against the generator's real R9 / R11 (and R12)
implementations, then authoring the draw. See the final report.
