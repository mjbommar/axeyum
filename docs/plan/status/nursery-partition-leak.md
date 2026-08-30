# Lane: nursery-partition-leak — the nursery split gate names what it finds

<!-- plan-section: lane-status -->

**Done** (`WIP`, nursery-partition-leak, 2026-08-30). `check-autogenesis-nursery.py`
went from `EXIT=1` with a bare, un-actionable header to `EXIT=0` naming every
crossing it forgives and why.

Diagnosed independently against `artifacts/autogenesis/nursery-v1.json` (not
inherited from a prior lane's report, which named the wrong facts): **3
declared-dependency components cross train/development, zero held-out
involvement**, plus a 4th/overlapping violation where 8 evaluation facts (7
train, 1 development) share a component with the Autogenesis-1 longitudinal
facts via `F:nat-mul-one`/`F:nat-zero-add`. Root cause: commit `237c1abdd`
(2026-08-29) retroactively added 1,054 real `depends_on` edges the
2026-08-18 freeze never saw. All 18 affected facts are independently verified
`epistemic_status: proved`, zero of the 29 registered autogenesis operations
reference any of them, and none are held-out.

Landed: `describe_leak()` renders every violation with full component/family/
shape/source-group membership and partitions, and `build_report` accumulates
ALL violation types into one message instead of raising on the first. A new
`component_split_exemptions` mechanism (self-invalidating: keyed on the exact
component digest recomputed from the CURRENT dependency graph, so it silently
stops applying the moment an exempted component grows) covers exactly the 3
diagnosed benign crossings, recorded and justified in
[ADR-0850](../../research/09-decisions/adr-0850-nursery-split-exemption-mechanism.md).
No amendment, no partition move, no fact edit — the crossing was a
bookkeeping gap the ledger-hygiene fix exposed, not a spent evaluation row.

Flagged in the ADR for a decision above this lane's level, not resolved here:
104/120 development and 72/78 train v1 entries are already `proved` against
0/16 held-out — consistent with train/development being meant for ordinary,
non-blind work, but nothing in ADR-0478 says so explicitly and no gate
measures it.

8 new tests added (19 total, all green); 6-guard mutation kill table below
— 5 guards killed exactly 1 test, 1 guard (`leaks` exemption filtering) killed
2 (both legitimately exercise the same suppression path from different
angles; not a vacuous-guard case).

<!-- plan-section: landed-changes -->

| 2026-08-30 | `847148d3a` | Status doc with root-cause diagnosis (first commit). |
| 2026-08-30 | `2cc851274` | `describe_leak()` + accumulated multi-violation messages; all 11 pre-existing tests pass unchanged. |
| 2026-08-30 | `713ae6b6e` | ADR-0850; `component_split_exemptions` field + validation; exempted the 3 diagnosed crossings in `nursery-v1.json`; gate exit 1 -> 0. |
| 2026-08-30 | `b4f02cd22` | 8 new tests covering detailed messages, multi-violation accumulation, and the exemption mechanism's schema/suppression/self-invalidation. |
