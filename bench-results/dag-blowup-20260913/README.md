# DAG-BLOWUP: the second A/B pass its lane declared as "did not run"

Lane `DAG-BLOWUP` (merged `6b548ef34`, ADR-1940) memoised **17 term walkers
across 10 modules**. Its own A/B covered QF_LIA, QF_UFLRA, QF_LRA and a QF_UF
control, and it recorded — rather than omitted — that a second pass over four
further divisions had not completed.

**This is that pass, run by the coordinator.** Pre-merge binary vs post-merge,
interleaved per file, arm order alternating per index, one pinned core per
division, 24 s budget.

| division | n | pre | post | gain | loss | **flip** |
|---|---:|---:|---:|---:|---:|---:|
| QF_IDL | 200 | 105 | 105 | 0 | 0 | **0** |
| QF_NIA | 200 | 72 | 73 | 1 | 0 | **0** |
| QF_NRA | 200 | 115 | 115 | 0 | 0 | **0** |
| QF_SLIA | 200 | 195 | 195 | 0 | 0 | **0** |
| **total** | **800** | | | **1** | **0** | **0** |

**Zero losses and zero `sat`↔`unsat` flips.** The flip column is the one that
matters: these memos sit on every linear-arithmetic route, so a wrong verdict
here would be a soundness defect, not a performance one.

**The +1 in QF_NIA is NOT claimed as a gain.** The lane measured that at a 24 s
budget with 4 workers roughly 1–1.5% of files flip on ambient load alone, and it
re-ran all eight of its own raw gains/losses four times each and found every one
decided identically in both arms. One file out of 800 is inside that band.

Combined with the lane's own pass, the 17 memos are now clean across **~1,470
files in 8 divisions**.

## Why this was worth running rather than accepting

The lane's verdict on its own work was "price this as robustness, not board
points" — it measured that 0 of 12,422 QF_LIA files and 0 of 1,594 rows across
seven other divisions carry ≥ 2²⁰ arithmetic paths. That makes the *upside*
narrow, which raises rather than lowers the value of bounding the downside: a
change with little to gain should be held to a strict no-regression standard
before it ships on ten modules.
