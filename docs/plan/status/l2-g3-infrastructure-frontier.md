# Lane: l2-g3-infrastructure-frontier — ADR-0717 L2 phase G3, publish the infrastructure frontier

<!-- plan-section: lane-status -->

**Done, l2-g3-infrastructure-frontier, 2026-08-30.**
[ADR-0845](../../research/09-decisions/adr-0845-the-infrastructure-frontier-curates-candidates-and-validates-them-live.md)
records the design decisions.

## What landed

Executed G3 of `docs/plan/graph-directed-library-roadmap-2026-08-30.md`:
four frozen queues over the L1 phase G2 graph join
(`artifacts/graph-join/mathlib-group-defs-v1.join.json`, ADR-0835), each
row carrying a stable content-hash id, raw evidence, a stated gain kind,
current blockers, destination paths, an estimated cost, and a
preregistered, re-runnable metric.

Detail moved to [`../notes/l2-g3-infrastructure-frontier.md`](../notes/l2-g3-infrastructure-frontier.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | `694f01952` | L2 phase G3: publish the infrastructure frontier -- four frozen queues over the group-defs population, content-hash row ids, seven mutation-verified guards (ADR-0845). |
