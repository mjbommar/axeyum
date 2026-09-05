# Lane: poly-commring — close `AlgS.Poly.*` into a full `AlgS.CommRing` (W2-9 residue)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, poly-commring, 2026-09-04).** ADR-1609 landed
`AlgS.Poly.*` 20 fields into the 23-field `AlgS.CommRing` record. The residue is
`mulOneL`, `mulOneR`, `mulComm`, `mulAssoc`, each blocked on a reindexing lemma
for the antidiagonal walk `AlgS.Poly.antidiagFrom`. This lane decides the
representation (walk vs a `sumRange`-with-`Nat.sub` restatement), proves the
three reindexing lemmas, and lands the instance plus concrete `Rat`/`Complex`
witnesses. ADR-1618.

<!-- plan-section: landed-changes -->

| 2026-09-04 | poly-commring | lane opened on the W2-9 residue: the four missing `AlgS.CommRing` fields of `R[X]` |
