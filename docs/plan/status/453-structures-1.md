# Lane: structures-1 — abstract algebraic structure spine (Magma..Field) as bundled kernel records

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, structures-1, 2026-09-03).** Starting: design
ADR-1578 for a `Magma -> Semigroup -> Monoid -> CommMonoid -> Group ->
CommGroup -> Semiring -> Ring -> CommRing -> Field` spine of one-constructor
`Sort 2` records (carrier field at `Sort 1`, per ADR-1495's universe finding),
then declare them, build ℕ/ℤ/ℚ instances, three generic theorems
(`mul_one_unique`, `neg_unique`, `mul_zero`) each instantiated at two
carriers, and attempt a generic `det_one` over an arbitrary `CommRing`
instantiated at ℚ against `Rat.det_one`. In progress; this stub records intent
before code.

<!-- plan-section: landed-changes -->

| 2026-09-03 | structures-1 | status stub only so far -- design and code follow |
