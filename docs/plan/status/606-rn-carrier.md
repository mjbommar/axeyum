# Lane: rn-carrier — ℝⁿ as a carrier (W2-4, convergence point C7)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, rn-carrier, 2026-09-04).** Building `RN.*`: ℝⁿ as
a setoid carrier over `Nat → CReal` with the dimension carried by the
equivalence relation (`RN.EqOn u v n := ∀ i, Nat.lt i n → CReal.Equiv (u i) (v i)`),
mirroring `Rat.dotN`'s already-landed "a vector is a coefficient function plus
an explicit bound" design (`rat_prelude::vector`). `Fin` does not exist in this
kernel outside one `nat_prelude` name lookup, and there is no `Subtype`/`Sigma`,
so the indexed-function-with-bound shape is the only one available. Inner
product, norm, Cauchy–Schwarz unsquared (generalizing
`Metric.CPoint.dotLeSqrtMul`), a `Metric` instance per dimension, and the
n = 2 bridge to `CPoint`. ADR-1606 records the design.

<!-- plan-section: landed-changes -->

| 2026-09-04 | rn-carrier | lane opened: ℝⁿ carrier design fixed on `Nat → CReal` + `EqOn n`, reusing `CReal.sumRange` |
