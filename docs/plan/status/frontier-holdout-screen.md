# Lane: frontier-holdout-screen — fix the two `held_out_fact_ids()` readers and the unscreened JSON selection path

<!-- plan-section: lane-status -->

**DONE, frontier-holdout-screen, 2026-09-01.** Fixed the defect in
[2026-09-01-the-selector-selected-a-held-out-fact.md](../../research/11-design-review/2026-09-01-the-selector-selected-a-held-out-fact.md):
`scripts/fact-frontier.py`'s `held_out_fact_ids()` read `nursery-v1.json`
literally and missed `nursery-v2-extension.json`'s 190 held-out rows, and its
one call site was the human-rendered queue line only -- the `--json` path
(`selection`/`admissible_fact_ids`/`diagnostics`) applied no held-out screen
at all.

Delegated `fact-frontier.py`'s `held_out_fact_ids()` to
`validate-producer-contracts.py`'s already-fixed glob reader (landed
2026-09-01, commit `45d605c4d`) instead of re-reading one manifest name, so
the two readers cannot drift apart again. Confirmed the union is 206 today
(v1's 16 + v2-extension's 190, no overlap). Added a `held_out` parameter to
`build_machine_frontier` that defaults to the real disk partition (same
asymmetry as `registry`, never the `contracts`/`declines` None-means-empty
side, since the screen must never be silently disabled by omission), folded
it into the admissibility loop with a named
`held-out-blind-evaluation-population` rejection reason, and surfaced
`diagnostics.held_out_fact_id_count`, `diagnostics.held_out_ready_count`, and
`selection.held_out_ready_fact_ids`. Confirmed via `--json`: the target fact
(`F:ml430-nat-coprime-factorizationlcmleft-factorizationlcmright-e7db70ce`)
now carries `held-out-blind-evaluation-population` in its `rejected_by`,
independently of the coincidental `gate-coupling-review-required` it also
still carries; `outcome` stays `refused-no-admissible-candidate`.

`SeedContractHoldoutIsolationTests` (`scripts/tests/test_validate_producer_contracts.py`)
already reads the glob (fixed same-day by `flywheel-restart`, commit
`45d605c4d` before this lane started); added
`test_synthetic_v2_style_manifest_is_detected`, a synthetic-manifest control
for that class's own detection logic.

Mutation-verified both new `fact-frontier.py` guards in an isolated snapshot
(`scripts/lane-snapshot.sh`, never the shared worktree):

| guard | mutation | baseline (78 tests) | mutant | killed |
| --- | --- | --- | --- | --- |
| multi-manifest read | `held_out_fact_ids()` reverted to reading `nursery-v1.json` only | 10 fail/error (pre-existing, see below) | 11 fail/error | exactly 1: `HeldOutFactIdsMultiManifestTests.test_the_real_union_equals_v1_plus_v2_extension_held_out_rows` |
| JSON-path screen | `is_admissible`/`reasons` no longer consult `held_out` | 10 fail/error | 11 fail/error | exactly 1: `JsonPathHeldOutScreenTests.test_a_held_out_fact_is_never_admissible_even_with_a_registered_operation` |

**Found, not fixed (out of scope): 10 pre-existing failures in
`scripts/tests/test_fact_frontier.py`, unrelated to this lane.** Confirmed
present against the pre-fix `fact-frontier.py` (commit `45d605c4d`) too, so
this lane did not cause them. Two separate real-ledger drifts: (1) the
`contract()` fixture helper is missing the `sizing` key ADR-1510 made
required on producer contracts, so every `ProducerContractAdmissibilityTests`/
`ProducerContractDeclineTests` case using it errors; (2)
`F:ml430-int-add-modeq-right-e58108ee` (used as `ProducerContractDeclineTests.TARGET`)
and `F:ml430-int-add-modeq-left-ee732b5b` (used in `RealDeclineFeedbackLoopTests`)
have since been proved, so tests asserting they are still open/admissible now
fail. `check-control-registration.sh` (exit 0, 316 python controls, 0
orphans) does not catch this because the suite runs and fails loudly, it is
not silently skipped -- but nothing gates on `python3 -m unittest
scripts.tests.test_fact_frontier` passing, so this went unnoticed. Worth a
follow-up lane.

`python3 scripts/validate-facts.py`: exit 0, 2576 facts checked, 0 errors.
`scripts/check-control-registration.sh`: exit clean, `orphans=0`,
`py_orphans=0`.

<!-- plan-section: landed-changes -->

| 2026-09-01 | `5db923e75` | status(frontier-holdout-screen): open the lane stub |
| 2026-09-01 | `f4df69696` | fix(frontier): screen held-out facts out of the JSON selection path, read every nursery manifest |
