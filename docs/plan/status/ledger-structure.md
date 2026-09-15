# Lane: ledger-structure — does the ledger show dispatch structure worth deriving into Phase 4?

<!-- plan-section: lane-status -->

**Lane ledger-structure (`DONE`, ledger-structure, 2026-09-15).** Phase 3
sizing for Phase 4 of
[dispatch-and-instrumentation-2026-09-15.md](../dispatch-and-instrumentation-2026-09-15.md#5-phase-4--derived-ladder-policy-conditional).
Filled the outcome ledger (ADR-2102, ADR-2105) over all seven Tier 1 pinned
200-file lists on `db31113fa`, 24 s / 8 GiB, `--trace` on, sharded 3 hosts x 4
core pairs (12 shards). **1,400 of 1,400 expected rows landed, 0 shortfall, 0
duplicates**, row count verified against each shard's own pinned list before
consolidation. Invariance control: 112/112 `ok`, 0 `MOVED`. Committed at
`bench-results/ledger/t1-<DIVISION>-db31113fa.tsv` (7 files, 200 rows each),
registered through `outcome_ledger.append_row`/`register`, never by hand.

**Answer: STRUCTURE on 5 of 12 (division, feature-class) groups** —
`AUFDTLIRA/not-dispatched`, `AUFLIRA/not-dispatched`, `QF_NIA/Int`,
`UFDTLIRA/not-dispatched`, `UFNIA/Int|Function` — by both the plan's literal
test and a harder "substantive first route" test that skips `fd:parse`'s
near-free bound probe (the two agree exactly on which 5). Full tables,
per-class ceilings (`prefix_cost_ms`), and the ranked Phase 4 recommendation
are in
[`bench-results/ledger-structure-20260915/README.md`](../../../bench-results/ledger-structure-20260915/README.md).
**Recommend Phase 4 run on `QF_NIA/Int` (631,307 ms prefix cost / 65 files)
and `UFNIA/Int|Function` (100% decision share, 126,764 ms / 24 files) first**;
the three `q:mbqi-quick` groups are real but two orders of magnitude smaller
(`AUFLIRA`'s ceiling is near-zero); the portfolio criterion (§5.2) found only
2 pairs at 4 and 1 rows out of 634 undecided — not structure, do not widen the
portfolio from this sample. Positive/negative controls checked in as a fixture
(`fixtures/synthetic_structure.tsv` + `test_analyze_structure.py`).

Caught and fixed one real analysis bug along the way (documented in
`analyze.py`'s own docstrings): route names in `attempt_trail` are not
colon-free (`fd:parse`, `q:mbqi-quick`, …), so splitting on the first colon
truncates every route name — must split on the last colon; and a route can
appear twice in one trail (`probe` then later `decided`), so matching by name
alone and stopping at the first hit misattributes the decision.

No Rust, no ADR — this lane answered one measurement question from the ledger
the Phase 3 lane already built.
