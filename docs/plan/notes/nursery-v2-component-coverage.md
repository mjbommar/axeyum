# Notes: nursery-v2-component-coverage

Detail moved out of [`../status/nursery-v2-component-coverage.md`](../status/nursery-v2-component-coverage.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Held-out involvement: none.** Verified directly — no member of any of the
3 crossing components has `partition == "held-out"`.

Confirmed the self-invalidating property already works as designed without
any code change: recomputing `digest()` for each of v1's 3 existing
`component_split_exemptions` entries against the **live union graph** shows
none of them match anymore (their named component grew by merging with v2
members) — exactly the fail-closed behaviour ADR-0850 specifies.

family/proof_shape/source_group leak checks: 0 crossings in the union
(checked as a diligence pass; not the primary target of this task).

## What landed

- `build_cross_population_report()` in `scripts/check-autogenesis-nursery.py`:
  the same weak-component-vs-evaluation-partition check as `build_report`,
  over `nursery-v1.json` entries UNION `nursery-v2-extension.json` entries.
  Wired into `main()` as a second hard gate (`AUTOGENESIS_NURSERY_CROSS_
  POPULATION_OK` line; script exits 1 if either check fails).
- Reuses `validate_entries`/`components`/`validate_exemptions`/`describe_leak`
  verbatim from ADR-0850 rather than a second mechanism. The exemption list
  is a new top-level `cross_population_component_split_exemptions` key in
  `nursery-v2-extension.json` (not touching `nursery-v1.json` or its own
  `component_split_exemptions`, and not touching `build_report`'s v1-scoped
  readiness/policy computation).
- `describe_leak` gained an optional `origin_of` parameter (tags each printed
  member `[v1]`/`[v2]`); every pre-existing call site is unaffected.
- Added the 3 exemption records (digests recomputed and matched against the
  live checker, never hand-transcribed), after independently confirming
  every one of the ~213 member facts across all three components is
  non-`held-out`.
- 10 new tests in `CrossPopulationTests` (`scripts/tests/
  test_check_autogenesis_nursery.py`), all 19 pre-existing tests pass
  unchanged (29 total, 0 failures).
- ADR-0855 records the decision and settles ADR-0850's open
  train/development question from the existing record (see below).

## Gate exit status

Before this change: `check-autogenesis-nursery.py` never examined
nursery-v2-extension.json at all (0 lines of code referenced it) — exit 0
proved nothing about it.

After: both checks run.
`AUTOGENESIS_NURSERY_OK|...|ready=true|evaluation=214|blockers=0` and
`AUTOGENESIS_NURSERY_CROSS_POPULATION_OK|...|v1=216|v2=340|components=295`,
script exit 0. Confirmed the cross-population check is NOT vacuous by
removing the 3 exemption records and re-running: exit 1, both violation
types (component-split and longitudinal-overlap) reported in full detail.

## Mutation guard -> test kill table

All mutations applied to a private snapshot of the file in this worktree
only, one at a time, restored from a pristine backup between each. Full
`python3 -m unittest scripts.tests.test_check_autogenesis_nursery` run after
each mutation.

| # | guard (line, mutated form) | test(s) killed |
|---|---|---|
| 1 | `kind != "...nursery-extension"` schema check -> `if False` | `test_wrong_extension_kind_is_rejected` (1) |
| 2 | `extends != "...nursery-v1.json"` check -> `if False` | `test_extension_must_still_declare_its_base` (1) |
| 3 | `if overlap:` (v1/v2 fact-id collision) -> `if False` | `test_overlapping_fact_ids_across_files_are_rejected` (1) |
| 4 | `leaks = [c for c in all_leaking_components if c not in exempted_component_ids]` -> `leaks = []` | `test_v2_internal_component_leak_fails_closed`, `test_cross_file_dependency_edge_creates_a_leak_invisible_to_either_file_alone`, `test_exemption_stops_matching_once_the_cross_population_component_grows` (3 — see note) |
| 5 | `if longitudinal_overlap_components:` (append violation block) -> `if False` | `test_cross_population_longitudinal_overlap_fails_closed_and_can_be_exempted` (1) |
| 6 | `origin_of=origin_of` on the component-leak `describe_leak` call -> `origin_of=None` | `test_cross_file_dependency_edge_creates_a_leak_invisible_to_either_file_alone` (1) |
| 7 | `"origin": origin_of[fact_id]` in the report's exempted-members list -> hardcoded `"v1"` | `test_exemption_suppresses_exactly_the_named_cross_population_component` (1) |
| 8 | `cross_population_component_split_exemptions_unused` comprehension -> hardcoded `[]` | **0 tests died on first try** — see below. Added `test_stale_exemption_matching_no_live_component_is_reported_as_unused`; re-ran the same mutation: `test_stale_exemption_matching_no_live_component_is_reported_as_unused` (1) |
| 9 | `entries_by_id` built from union -> built from `v1_entries` only | `test_exemption_suppresses_exactly_the_named_cross_population_component`, `test_exemption_stops_matching_once_the_cross_population_component_grows`, `test_cross_population_longitudinal_overlap_fails_closed_and_can_be_exempted`, `test_stale_exemption_matching_no_live_component_is_reported_as_unused` (4 — every test whose exemption names a v2 fact) |
| 10 | `if violation_blocks:` (top-level raise trigger) -> `if False` | all 4 fail-closed scenario tests (4 — the final gate every failing scenario depends on) |

**Guard 8 is the one that actually mattered.** The first cut of the "unused
exemptions" reporting field passed mutation with the existing test suite
(0 kills) — my own tests only ever checked it was `[]` in scenarios where it
was trivially `[]` regardless of the logic, exactly the checker-that-cannot-
fail shape this repository's CLAUDE.md warns about. Added a dedicated test
with a genuinely stale exemption (names two facts that are not, in fact,
connected to each other, so its digest matches no live component) before
re-measuring; the guard then dies as guard #8 above shows.

**Guards 4, 9, and 10 kill more than one test each, and that is a measured
fact, not a shortcut.** All three sit on code paths several independent
scenarios legitimately share (the core leak-detection list, the union-vs-v1
exemption lookup, and the single top-level raise), the same way `build_report`'s
equivalent lines (`leaks = [...]`, `if violation_blocks:`) are exercised by
multiple tests in the pre-existing `NurseryTests` suite. I did not force an
artificial 1:1 split across scenarios that are honestly testing the same
underlying mechanism from different angles; every one of these mutations
still kills at least one test, so none of the three is a checker that cannot
fail — the repository's actual concern.

## Held-out involvement

**None**, in either the raw diagnosis or after the fix. Every member of all
3 crossing components was checked directly against its `partition` field;
zero are `held-out`. No held-out row's partition was moved, no fact's
`epistemic_status` was touched, and `check-autogenesis-holdout-isolation.py`
(out of this lane's scope, read-only) already unions both `nursery-v1.json`
and `nursery-v2-extension.json` for its own held-out isolation check — that
gap does not exist for held-out; it only existed for the declared-dependency
component-split check this lane closes.

## Train/development invariant: settled, not gated further

ADR-0850 left open whether train/development being mostly `proved` already
(104/120 v1 development, 72/78 v1 train, vs 0/16 held-out) undermines
whatever measurement train/development are for. Settled from the existing
record (full evidence and citations in ADR-0855):

- ADR-0542 states directly that spent rows "remain fully usable in
  development, where looking is allowed" — development is explicitly not a
  blind population.
- `check-autogenesis-holdout-isolation.py`'s two rules ("no held-out fact may
  be settled", "no artifact may reference a held-out fact id") name only
  held-out; train/development settlement is unrestricted by design, not by
  omission.
- Every ADR-0542 amendment moves a family OUT of held-out INTO development,
  never the reverse and never involving train — consistent with held-out
  alone being the spendable, non-renewable blind resource.

**No new gate was added for this**, because the enforcement the evidence
calls for already exists exactly where it should (held-out isolation, which
already covers both nursery files) — a gate restricting train/development
settlement would contradict ADR-0542's own explicit design rather than
complete it. This is written down in ADR-0855 as the closing of ADR-0850's
open question, not left open.

## What is still unchecked about these populations

`check-autogenesis-nursery.py`'s family/proof_shape/source_group leak checks
were run over the union as a diligence pass (0 crossings found) but are
NOT extended by this change the way the component-split check is — a
cross-population family/shape/source-group leak would currently only be
caught if it also happens to coincide with a declared-dependency crossing.
Nothing found one in the current data, but that is a measurement of today's
data, not a standing guarantee the way the component check now is.
