# 351 — nursery draw 6b

<!-- plan-section: lane-status -->

**IN PROGRESS. The headline finding is measured and stands: the unblock
CONTAMINATED one of the two families it was meant to open.** Still to do:
the constant sweep that names draw 7's unblock, and the closing gates.

ADR-0645 declined draw 6 and named `Nat.dist` + `Nat.nth` as the exact
unblock, reporting `R9 name screen 0 of 18` for `Mathlib.Data.Nat.Dist`.
That was measured before `Nat.dist` existed. `nat_prelude/dist.rs` declares
the definition **and seven theorems**, five of which are exact Mathlib
mirror names in the Dist pool, and two of those five —
`Nat.dist_comm`, `Nat.dist_self` — land in the alphabetically-first ten a
draw takes. So the R9 name screen is now **2 of 10**, not 0 of 18.

Measured against the real generator, not argued: `select` + `guard` run in
memory over the current tree refuse the draw.

    GUARD REFUSED: R9 2 held-out candidate(s) already have a declaration of
    the same Mathlib name in the kernel environment, so they are not blind:
    [('natural-distance', 'Nat.dist_comm'), ('natural-distance', 'Nat.dist_self')]

Control, same machinery, Dist moved to development: `GUARD PASSED -- 300
entries, 120 held-out`. So R9-on-Dist is the single mechanical blocker and
`Mathlib.Data.Nat.Nth` is fully held-out-safe (R9 **0 of 11**).

Selection is `pool[:PER_FAMILY]` over a name-sorted pool, and `Nat.dist_comm`
sorts fourth, so no choice of module tuple can dodge it.

## Numbers re-derived for THIS draw, not carried from ADR-0645

| quantity | ADR-0645 | this run |
| --- | --- | --- |
| env declarations | 2,207 | **2,374** |
| bridge constants | 72 | 72 |
| drawable (generator screens) | 2,155 | **2,295** |
| un-owned modules at the floor | 11 | **10** |
| `Mathlib.Data.Nat.Dist` | 18 | 18 |
| `Mathlib.Data.Nat.Nth` | 11 | 11 |

The proposer reports **17** ready families; the generator yields **10**.

Baseline `check-dispatchable-frontier.py`: exit 1,
`FAIL: G7 queue-below-floor: 6 dispatchable mirror(s), floor 10`.
