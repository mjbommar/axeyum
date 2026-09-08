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

**Measured: 113 governing values registered, 24 dated (21%), 89 undated.**
Zero genuinely stale. **35 of 113 change behaviour with no branch and no signal
to the caller** — each now names what guards it, a question that previously had
no field to be answered in. No verdict moves: 155 files across `corpus/micro`
and `corpus/regression`, recording off and on, zero differences.

The staleness check is real: dating `MAX_ONLINE_LRA_ATOMS` 2026-08-03 — its true
original date — reproduces the thirteen-month failure in one command. Its own
positive control found three defects in it, two of which made it structurally
unable to fire while printing exactly what a working one prints.

## Landed

| Change | SHA |
| --- | --- |
| Lane status file and diary; the enumeration filter fixed up front | `0e64e41bb` |
| The registry: 113 entries, four checks, two self-imposed invariants (ADR-1762) | `0e77c7346` |
| `scripts/check-config-registry-staleness.py` plus its positive control | `a0b60ddd9` |
| `--trace` emits the configuration; four gates record what they consulted | `8a4c96efc` |

## Owed at merge

`scripts/gen-plan.py` has NOT been run (per the brief). `gen-plan.py --check`
passes with this file removed and fails with it present, so the regeneration is
owed and is caused by nothing else. The duplicate ADR numbers
`check-merge-hygiene.sh` reports (0166, 0167) are pre-existing on `main` and are
not this lane's.

## Findings recorded, NOT fixed

This lane reads and registers; it retunes nothing. Seven findings are in
ADR-1762, including two same-name/same-value constant pairs with different
contracts (`MAX_CONGRUENCE_GROUPS`, `MAX_CERTIFIABLE_BOOLS`), a budget-sharing
policy that is bypassed silently when the share underflows
(`auto::INT_REAL_RELAX_BUDGET_SHARE`), and a size gate whose refusal is
indistinguishable from a structural decline (`dl_online::MAX_DL_ATOMS`).
