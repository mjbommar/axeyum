# Lane: graph-carrier — a finite graph carrier over `Nat.Finset`, Ramsey R(3,3), Hall

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, graph-carrier, 2026-09-04).** Roadmap W1-6, W2-11,
W2-12; ADR-1608. Building `Nat.Graph` as a decidable adjacency relation on a
bounded vertex range — the exact sibling of `Nat.Finset` (ADR-1577) — then
degree, neighbourhoods as `Nat.Finset`s, walks and connectivity; then Ramsey
for two colours (`R(3,3) = 6` if the general statement is out of reach); then
Hall's marriage theorem over `Nat.Finset` through the existing
`card_le_of_injOn`. Lane opened; nothing admitted yet.

<!-- plan-section: landed-changes -->

| 2026-09-04 | graph-carrier | lane opened for the graph carrier, Ramsey and Hall (ADR-1608) |
