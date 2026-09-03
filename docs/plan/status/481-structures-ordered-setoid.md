# Lane: structures-ordered-setoid — AlgS.Group-level theorems and AlgS.OrderedRing, so linarith::generic reaches ℝ

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, structures-ordered-setoid, 2026-09-03).** Starting
point: ADR-1590 named two open gaps — no `AlgS.Group`-level generic theorem
(so `Alg.neg_neg` cannot derive from `AlgS`), and no `AlgS.OrderedRing` at
all (so `linarith::generic`, ADR-1585, cannot reach `CReal`). This lane
closes both. In progress; see below for what has landed.

<!-- plan-section: landed-changes -->

| 2026-09-03 | structures-ordered-setoid | status stub opened |
