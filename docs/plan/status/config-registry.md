# Lane: config-registry — the solver's configuration surface, enumerated, recorded and dated

<!-- plan-section: lane-status -->

**`WIP`, config-registry, 2026-09-07.** The solver's behaviour is governed by
dozens of caps, bounds, budgets and thresholds held as private constants.
Nothing enumerated them, nothing recorded which values a run used, and their
justifications went stale silently. Four measured instances in two days, all of
which are now cited in [ADR-1762](../../research/09-decisions/adr-1762-the-configuration-surface-is-enumerable-recordable-and-dated.md):

- `MAX_ONLINE_LRA_ATOMS = 1_024` rested on a 2026-08-03 measurement of an 8 GiB
  abort. The bound that caps exactly that cost landed **2026-08-06 — three days
  later** — and the measurement was never re-taken. Replaced by
  [ADR-1752](../../research/09-decisions/adr-1752-the-lra-admission-cap-becomes-budget-relative.md).
- The QF_NRA cross-product bound metered in **cross-products** while the engine
  consuming its output meters in **atoms**: two gates, incommensurable units,
  15x apart ([ADR-1751](../../research/09-decisions/adr-1751-nra-admission-is-the-consumers-capacity.md)).
- `MAX_CONGRUENCE_GROUPS = 48` changes soundness mode above the cap with **no
  branch and no signal to the caller**.
- A cap whose rationale said the code OOM-killed the host at 64 GiB re-measured
  at 3.3 GiB peak and zero aborts in 124 runs.

**This lane reads and registers. It does not retune.** No constant's value
changes. Full record: [the diary](../../research/12-performance/config-registry-2026-09-07.md).

## Landed

(rows appended as they land)
