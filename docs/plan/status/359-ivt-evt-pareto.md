# 359 — IVT/EVT Pareto audit

<!-- plan-section: lane-status -->

**Status: DONE.** Measurement task, not a build task. **No fact was
reclassified, reopened or edited.**

## The answer

The Pareto claim holds **for IVT** and **not for EVT**.

| ADR-0603 row | IVT | EVT |
| --- | --- | --- |
| 1 general constructive | `CReal.ivt_approx` — genuine | **ABSENT** (`CReal.supOn` not in the environment) |
| 2 boundary refutation | `CReal.ivt_exact_root_decides_sign` — survives a harsh reading | `CReal.evt_attained_max_decides_sign` — theorem sound, ledger evidence thin |
| 3 decidable fragment | CAS; substantive half is `cas-internal` | CAS; substantive half is `cas-internal` |
| 4 labeled import | **ABSENT** | **ABSENT** |

EVT is a refutation of the classical statement with nothing constructive
standing in its place, so it is a trade rather than a dominance:
Mathlib's `IsCompact.exists_isMaxOn` proves EVT for an arbitrary compact subset
of an arbitrary topological space and we prove nothing positive at all.
`creal/supremum.rs` already says `CReal.supOn` is "still not landed"; nothing in
the ledger or in `07-the-cost-model-and-pareto-position.md` records that EVT is
being cited as a dominance example while its row 1 is missing.

## Deliverables

- Audit: `docs/formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md`
- Decision: `docs/research/09-decisions/adr-0675-evt-is-a-refutation-with-no-row-one-behind-it.md`
- Instruments committed beside them: `scratch-probe.sh`, `scratch-ivt-dump.py`,
  and the raw `scratch-inventory.txt` / `scratch-ivt-types.txt` they produced.

## Also found

Detail moved to [`../notes/359-ivt-evt-pareto.md`](../notes/359-ivt-evt-pareto.md).

