# Lane: echelon-invariant-2 — ADR-1554 obligation 4: the echelon loop invariant and the unconditional rank bridge

<!-- plan-section: lane-status -->

**echelon-invariant-2 (`WIP`, 2026-09-02).** Picking up exactly where ADR-1571
§3's table stopped: `Rat.rowSwap` preserving a zero range over `[pr, rows)` is
the one missing prerequisite, then the invariant as an explicit predicate with
its fuel induction over `echelonAux`, then the exit derivation over
`isEchelonAux`'s own fuel. The payoff is `Rat.rowEchelon_isEchelon`, the pivot
section, and discharging the three `_of_pivotSection` bridges into unconditional
`Rat.rank_eq_rankCols`, `Rat.rank_le_cols` and the row-form rank-nullity.

Nothing landed yet beyond this stub.

<!-- plan-section: landed-changes -->

| 2026-09-02 | echelon-invariant-2 | lane opened; obligation 4 picked up from ADR-1571 §3 |
