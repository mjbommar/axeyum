# Lane: rank-bridge — the `Rat.rank = Rat.rankCols` bridge (ADR-1554 obligation 4)

<!-- plan-section: lane-status -->

**WIP (`rank-bridge`, 2026-09-02).** Opened. Target: the pivot-row ↔
pivot-column correspondence under the rank bridge — `Rat.pivotRowOfCol` as a
computed `Definition`, `pivotSearch`/`clearBelow` postconditions, the echelon
loop invariant, then `Rat.rank_eq_rankCols` through `Nat.countRange_bij`
(landed 2026-09-02 by lane 422). Nothing landed yet.

<!-- plan-section: landed-changes -->

| 2026-09-02 | rank-bridge | lane opened; status stub only |
