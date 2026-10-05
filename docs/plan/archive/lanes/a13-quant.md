# Lane: a13-quant — nested-binder activation for UFLIA/AUFDTLIRA (ADR-2149)

<!-- plan-section: lane-status -->

**Lane A13-QUANT (`STOPPED-BY-COORDINATOR`, a13-quant, 2026-09-17).**
Resume-queue item 4 of the five-divisions stock-take. **Deliverable 1 MET:**
the two fixtures decided QUANT-COMPOSE's reading against its strong form —
the static registration of a universal under a crossed binder IS inert and
its tuples ARE dropped (now counted in a `crossed-binder` class), but the
engine activates the universal anyway through `NestedDiscovery::scan`
(ADR-2120 slice 3), which re-registers it against the enclosing universal's
instance: z3's `qi_queue.cpp:336` route, already built. The brief's fixture
(a) is not the crossed shape (the outer prefix is peeled before the walk); its
level-0 block is ADR-2120's `=>` whitelist and the front door refutes it at
level 0. **Deliverable 2 MET:** the 53-core split
(`bench-results/quant-nested-activation-20260917/split.tsv`): shipped arm
17,685 crossed / 0 negative / 2,520,232 untracked drops (crossed on 5
cores); at `AXEYUM_QINST_POSITIVE_PATH=1` 1,611,516 crossed on 9 cores /
231,040 negative / 57,014 untracked, with 13.7 M contextful tuples cut by the
per-round handoff cap, the discovery cap hit on 26 of 53 cores, 17,600
handoffs refused for binding a variable to itself; the table now prints at
every loop exit (37 of 53 cores, was 18). **Deliverable 3 MET, OFF:**
`AXEYUM_QINST_NESTED_ACTIVATION` — level 1 scans staged replacements before
plain instances and counts only first-time conclusions against
`MAX_POSITIVE_INSTANCES`; level 2 ingests a quantifier inside a ground formula
as one opaque leaf. Two earlier level-1 rules that SKIPPED instance-exposed
registrations each lost `TokenQueue.576` and are recorded as refuted. 22
tests, 6 mutation guards each killing a named test, anchors stale=0.
**Deliverable 4 PARTIAL:** six arms, runs 1 and 2 complete (636 rows), run 3
stopped at 32/53 `off` and 28/53 `on` when the coordinator paused the
campaign. Alone the lever moves nothing (15/15 vs `off` 15/16); composed with
ADR-2120 + ADR-2130 it gains `TypeDeclElemPragma.373` (2/2 vs 0/3) and loses
`TokenQueue.576` (0/2 vs 3/3), an interaction between level 2's ingestion and
ADR-2120's level 1. **Deliverable 5 NOT RUN** (pinned A/B, UFNIA control,
held-out draws): the composed arm's one-for-one does not clear the bar, and
the campaign is paused. ADR-2149 `proposed`, lever OFF. Next single
increment: the `AXEYUM_QGROUNDDUMP` diff between the `on` and `nested2-on`
arms on `TokenQueue.576`.

<!-- plan-section: landed-changes -->

| 2026-09-17 | `faa6cac11` | ADR-2149 deliverable 1: `quant_nested_activation_2149.rs` (the brief's two fixtures plus the genuinely crossed shape), `InertReason` split of `inactive_dropped`, `NestedActivationStatsGuard`, the per-universal census at every loop exit and across rebuilds. |
| 2026-09-17 | `863db1295` | ADR-2149 deliverables 2–3: the 53-core split (`bench-results/quant-nested-activation-20260917/`), `AXEYUM_QINST_NESTED_ACTIVATION` (OFF), mutation family `qinst-nested-activation`. |
| 2026-09-17 | `d95d9c75d`, `26c81da53` | Two level-1 rules that skipped instance-exposed registrations refuted by the sweep (`TokenQueue.576`) and replaced by a scan order + a budget counter; ADR-2149 records both. |
| 2026-09-17 | (this commit) | The six-arm sweep, runs 1–2 complete and run 3 partial (`sweep.tsv`), ADR-2149 §6 and consequences, README, status. Lever OFF, ADR `proposed`. |
