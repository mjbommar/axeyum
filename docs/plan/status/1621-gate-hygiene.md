# Lane: gate-hygiene — bring check-absence-claims.py green, correct stale sqrt-absence comments

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, gate-hygiene, 2026-09-04).** Starting work: (A)
`scripts/check-absence-claims.py` is RED on main (206 bare claims vs budget
122, 2 EXPIRED: `Rat.prodRange`, `Nat.factorization`) — resolving the expired
claims and annotating bare ones down toward budget. (B) five-plus stale
"no sqrt" / "not expressible" doc comments in `creal_point.rs` and
`CPointPrelude::cauchy_schwarz`, false since `CReal.sqrt` and
`Metric.CPoint.dotLeSqrtMul` landed — correcting doc comments only, no code.

<!-- plan-section: landed-changes -->

| 2026-09-04 | gate-hygiene | what landed, in one line |
