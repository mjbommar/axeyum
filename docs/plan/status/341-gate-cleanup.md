# Lane 341 — gate cleanup: the 43 `check-fast` failures

<!-- plan-section: lane-status -->

**Status: done.** Per-step detail in
[`docs/plan/notes/341-gate-cleanup.md`](../notes/341-gate-cleanup.md).

    before   declared=404|ok=248|failed=43|deferred=113
    after    declared=405|ok=273|failed=17|deferred=115

All 43 were re-run at merged HEAD first and all 43 still failed, so none was a
stale-list artifact. **26 no longer fail** — 24 fixed, plus 2 reclassified as
host-conditional and deferred. **17 left red with reasons.**

The one real defect: a spurious `depends_on` back-edge made the fact DAG cyclic
(`log_mono_right` <-> `log_monotone`), which exited `gen-autogenesis-baseline.py`
at 2 and froze every artifact downstream of it. The source settles the direction
and the `clog` pair is the positive control.

The largest group was drift, and its size is the finding: ten generated views
were describing a **698-fact** ledger against an actual **2,220**.
`facts_via_multi_target` did NOT rise with them — 30 before and after.

Three fixes were real defects rather than drift: a census that had crashed on
every run for six days, a check reading only the first occurrence of each claim
it gates, and two CI revisions pinned under keys naming no repository.

**Held-out is intact and was never touched.** Neither nursery manifest is
modified in any commit here:

    AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1106|settled=0|references=0|verdict=PASS

Deliberately still red: `autogenesis-nursery` (three `depends_on` components
span development/train — none reaches held-out; the fix is an ADR-0542
amendment, not gate work), `development-partition`, `mobility-census` (3 real
violations another lane kept red today), `local-ci-freshness` (needs a real CI
run), `plan-authority` (systemic, 1.98 MB of status files), `obstruction-graph`
(an unclassified decline shape it correctly refuses to drop), and six pinned
counts I could not verify as legitimate moves.

<!-- /plan-section -->
