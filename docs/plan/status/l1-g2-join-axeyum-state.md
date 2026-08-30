# Lane: l1-g2-join-axeyum-state — ADR-0717 L1 phase G2, join the declaration graph to Axeyum's own state

<!-- plan-section: lane-status -->

**Done, l1-g2-join-axeyum-state, 2026-08-30.** [ADR-0835](../../research/09-decisions/adr-0835-the-graph-join-resolves-identity-only-through-an-existing-ledger-mirror.md)
records the design decisions.

## What landed

Executed G2 of `docs/plan/graph-directed-library-roadmap-2026-08-30.md`:
joined ADR-0820's declaration graph (446 declarations, population
`mathlib-group-defs-v1`) to seven dimensions of Axeyum's own state, with
every dimension's population, resolved and unresolved counts reported
explicitly.

Detail moved to [`../notes/l1-g2-join-axeyum-state.md`](../notes/l1-g2-join-axeyum-state.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | `0e6a1cf15` | L1 phase G2: join the Mathlib declaration graph to ledger facts, kernel declarations, statement vocabulary, destination nodes, producers, declines and trust footprints (ADR-0835). |
