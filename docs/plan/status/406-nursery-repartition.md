# Lane: nursery-repartition — option 1 from ADR-1546: partition the nursery by connected component of the live dependency graph

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, nursery-repartition, 2026-09-02).** ADR-1546 left
three repair options; lane `partition-edge-gate` took option 2 (ADR-1550,
`scripts/check-partition-edges.py`, 198 crossing edges baselined and ratcheted
so the baseline may only shrink). This lane takes **option 1**: re-partition the
already-drawn rows by connected component of the declared-dependency graph,
under a rule preregistered in ADR-1551, so the recorded crossing count shrinks
toward zero and the seven component exemptions can be deleted rather than
enlarged. Held-out rows never move out of held-out. Status: measuring
components.

<!-- plan-section: landed-changes -->

| 2026-09-02 | nursery-repartition | status stub; lane opened on ADR-1546 option 1 (component-based re-partition) |
