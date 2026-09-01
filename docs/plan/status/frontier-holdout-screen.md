# Lane: frontier-holdout-screen — fix the two `held_out_fact_ids()` readers and the unscreened JSON selection path

<!-- plan-section: lane-status -->

**WIP, frontier-holdout-screen, 2026-09-01.** Fixing the defect in
[2026-09-01-the-selector-selected-a-held-out-fact.md](../../research/11-design-review/2026-09-01-the-selector-selected-a-held-out-fact.md):
`scripts/fact-frontier.py`'s `held_out_fact_ids()` read `nursery-v1.json`
literally and missed `nursery-v2-extension.json`'s 190 held-out rows, and its
one call site was the human-rendered queue line only -- the `--json` path
(`selection`/`admissible_fact_ids`/`diagnostics`) applied no held-out screen
at all.

Plan: delegate `fact-frontier.py`'s `held_out_fact_ids()` to
`validate-producer-contracts.py`'s already-fixed glob reader (landed
2026-09-01, commit `45d605c4d`) so the two can't drift apart again; add a
`held_out` parameter to `build_machine_frontier` that defaults to the real
disk partition (same asymmetry as `registry`, never the `contracts`/
`declines` None-means-empty side); screen it into the admissibility loop
with a named rejection reason; surface `held_out_fact_id_count` /
`held_out_ready_count` / `held_out_ready_fact_ids`. Then mutation-verify both
new guards in an isolated snapshot.

<!-- plan-section: landed-changes -->
