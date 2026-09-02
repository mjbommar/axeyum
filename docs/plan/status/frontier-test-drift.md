# Lane: frontier-test-drift — fix the 10 pre-existing failures in `scripts/tests/test_fact_frontier.py`

<!-- plan-section: lane-status -->

**DONE, frontier-test-drift, 2026-09-01.** Fixed the 10 pre-existing
failures (`failures=3, errors=7`, confirmed exact match on `main`) that
`docs/plan/status/frontier-holdout-screen.md` found but left unfixed.

Starting point: worktree was branched from an older `main`, 47 commits
behind (missing ADR-1510 itself, `307e5d2e6`). Merged local `main`
fast-forward-clean (no conflicts) before reproducing, landing at `5d03dd4f6`,
so the fix is against current `main`, not the stale branch point.

**Per-test cause table (all 10, confirmed individually, not assumed from the
prior lane's diagnosis):**

| test | class | cause |
| --- | --- | --- |
| `test_ambiguous_producer_contract_match_is_not_admissible` | `ProducerContractAdmissibilityTests` | ERROR: `contract()` fixture missing ADR-1510 `sizing` key |
| `test_matched_contract_with_capable_route_is_admissible` | `ProducerContractAdmissibilityTests` | ERROR: same |
| `test_matched_contract_with_incapable_route_is_not_admissible` | `ProducerContractAdmissibilityTests` | ERROR: same |
| `test_no_route_fact_is_never_admissible_via_contract` | `ProducerContractAdmissibilityTests` | ERROR: same |
| `test_declines_default_to_none_not_auto_loaded` | `ProducerContractDeclineTests` | FAIL: hard-coded `TARGET = F:ml430-int-add-modeq-right-e58108ee`, now `proved` |
| `test_live_decline_removes_admissibility_and_reports_declined` | `ProducerContractDeclineTests` | ERROR: same drifted `TARGET`, decline against a settled fact needs an ADR-1510 `resolution` block |
| `test_shape_matched_count_is_unaffected_by_a_decline` | `ProducerContractDeclineTests` | ERROR: same |
| `test_stale_decline_against_a_changed_contract_does_not_suppress` | `ProducerContractDeclineTests` | ERROR: same |
| `test_the_declined_fact_is_no_longer_selected` | `RealDeclineFeedbackLoopTests` | FAIL: hard-coded `F:ml430-int-add-modeq-left-ee732b5b`, now `proved` |
| `test_real_seed_contracts_move_admissible_off_zero` | `RealSeedProducerContractTests` | FAIL: **not** sizing/drift — the real ledger's contract-admissible population is genuinely 0 right now (see below) |

**A third, previously undiagnosed root cause**, found by not assuming the
prior lane's 2-cause diagnosis was complete (per this lane's brief):
`test_real_seed_contracts_move_admissible_off_zero` asserts
`admissible_via_contract_count > 0` against the real ledger with the real
seed contracts and no declines — genuinely `0` today, confirmed directly
against `frontier.build_machine_frontier`, independent of the sizing fixture
and the two proved targets. Two real, current, orthogonal facts: (1)
`int-modeq-family-v1` closed its whole matched family and now carries a
`retirement` block (0 live population); (2) `nat-coprime-family-v1`'s one
remaining live candidate, `F:ml430-nat-coprime-of-lt-minfac-0f79bdba`, is
blocked by an unrelated `gate-coupling-review-required` finding
(`gen-obstruction-producers.py` names it — real gate coupling, not a false
positive). Separately, every real committed decline against either seed
contract went stale the moment ADR-1510 added a `sizing` block to both
contract files, by the re-dispatch policy's own design (editing a contract's
content auto-reopens what it declined) — so `declined_fact_ids` over the
real declines alone is also currently empty, which is why
`RealDeclineFeedbackLoopTests` needed the same treatment.

**Fix approach**, honoring the brief's constraints (no touching the two
proved facts, any nursery manifest, any held-out fact, or any contract):

- `contract()` test fixture (`ProducerContractAdmissibilityTests`,
  `ProducerContractDeclineTests`'s sibling fixtures): added a valid `sizing`
  block (count 0, since the fixture's `id_prefix` never matches a real fact)
  and the `retirement` block ADR-1510 rule 1(b) then requires for a
  zero-population contract.
- Added `derive_contract_admissible_target` (real-ledger-first, synthetic
  in-memory-only fallback) and `derive_contract_path_target` (real-fact-only,
  narrower contract-path level — a decline can only ever validly name a real
  committed fact id, so it cannot use the synthetic fallback) to
  `scripts/tests/test_fact_frontier.py`. Every previously hard-coded
  `TARGET`/declined-fact literal is now derived from the live ledger at test
  time instead (CLAUDE.md: "a test relying on 'an X exists' must derive its
  X from the authority, not a literal").
- `ProducerContractDeclineTests` now asserts at the CONTRACT-PATH level
  (`declined_producer_contract_ids`, `declined_fact_ids`,
  `declined_by_contract`, `declined_count`) rather than full pipeline
  `admissible_fact_ids`, since the one real fact with an open contract path
  today is separately gate-blocked — matches the engine's own documented
  separation between the two populations, so nothing was weakened to force a
  pass.
- `RealSeedProducerContractTests` and `RealDeclineFeedbackLoopTests` fall
  back to one synthetic, in-memory-only fact (never written to disk) shaped
  to match a real, non-retired contract, only when the real population is
  empty — reverts to the real-ledger branch automatically once it
  repopulates.

**Result:** all 10 originally-failing tests now pass, run individually
(`ProducerContractAdmissibilityTests` 5/5 in 0.8s,
`RealSeedProducerContractTests` 2/2 in 40s, `ProducerContractDeclineTests`
5/5 in 134s, `RealDeclineFeedbackLoopTests` 1/1 in 25s). The remaining 13
tests in the suite (`MachineFrontierTests`,
`HeldOutFactIdsMultiManifestTests`, `JsonPathHeldOutScreenTests`, and the
untouched methods in the classes above) were not modified and were already
green in the pre-fix baseline run.

**Did not run: the whole-suite aggregate `python3 scripts/tests/test_fact_frontier.py`
in one invocation.** Each real-ledger call reloads and re-validates the full
fact/contract/decline set from disk, and the suite now makes more such calls
than before (the derivation helpers each build one extra frontier snapshot);
one full run exceeded the 5-minute bound and was stopped
(`TaskStop`) rather than left to poll in the background, per this lane's
brief. The per-class runs above are the evidence instead; each ran to
completion with an explicit exit code, and every non-fixed class was
confirmed green in the last complete full-suite run before these edits
(`failures=3, errors=7`, exactly the 10 above, 23 tests total).

`scripts/check-control-registration.sh`: exit 0,
`controls=51|orphans=0|py_controls=316|py_orphans=0`.
`scripts/tests/mutation_controls.py` has no entries for `fact-frontier.py`
or `scripts/tests/test_fact_frontier.py` (only for
`validate-producer-contracts.py` and
`validate-producer-contract-declines.py`, unrelated to this fix) — nothing
to run there.

<!-- plan-section: landed-changes -->

| 2026-09-01 | `34a62b02d` | status(frontier-test-drift): open the lane stub |
| 2026-09-01 | (pending) | fix(frontier): derive test_fact_frontier's real-ledger targets at test time, add ADR-1510 sizing to the contract fixture |
