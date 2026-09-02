# Lane: heldout-construction-1 — declare one held-out-safe construction so draw 19 has a module-disjoint pair

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, heldout-construction-1, 2026-09-02).** ADR-1556
refused draw 19 on measurement: 3 viable held-out families, all drawing from the
same four modules, so R5's two module-disjoint held-out families cannot be met.
Its named unblock is ADR-1420 Route 1 — a construction lane declaring ONE
held-out-safe module disjoint from `{Factorization.Basic, IntervalCases,
PythagoreanTriples, SumTwoSquares}`. This lane declares the CONSTRUCTION only:
definitions, evaluation tests, defining equations (`refl`). No theorem about the
construction is proved here; every such theorem is a candidate held-out row and
proving one spends it.

Module choice and screen recorded in ADR-1559 before any Rust is written.

<!-- plan-section: landed-changes -->

| 2026-09-02 | heldout-construction-1 | lane opened: status stub, scope fixed to construction-only per ADR-1420 Route 1 |
