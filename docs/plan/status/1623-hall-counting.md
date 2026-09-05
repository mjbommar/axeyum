# Lane: hall-counting — the counting half of Hall's marriage theorem (W2-12)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, hall-counting, 2026-09-05).** ADR-1614 closed the
choice problem (`Nat.Finset.anySubset` + both reflection polarities) and moved
the obstruction to the FAMILY. This lane takes the counting half, in order:
`unionOver` congruence and bound-independence; `unionOver` under family
modification (`nb' i := sdiff (nb i) U`) and `card` of an `sdiff`; the matching
union on disjoint images; and Hall's sufficiency by `Nat.strongInduction` if the
three land. ADR-1623 is reserved. A precise stopping point is a complete
deliverable, as it was for ADR-1608 and ADR-1614.

<!-- plan-section: landed-changes -->

| 2026-09-05 | hall-counting | lane opened; ADR-1623 reserved for the counting half of Hall |
