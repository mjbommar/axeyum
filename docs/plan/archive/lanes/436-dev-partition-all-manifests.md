# Lane: dev-partition-all-manifests — fix two v1-only nursery readers (gate-hygiene lane 2)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, dev-partition-all-manifests, 2026-09-02).** Both
defects fixed and both suites green.

**Fix 1.** `scripts/check-development-partition.py` read `nursery-v1.json`
alone (`NURSERY` constant); the four `development` facts
`authoritative-mathlib-nat-bit-constructor-family-v1` (ADR-1570) closed live
only in `nursery-v2-extension.json`, so the gate's dev-without-train rule
never saw the operation and printed PASS. Replaced with `NURSERY_DIR` +
`MANIFEST_GLOBS = ("nursery-v1.json", "nursery-v*-extension.json")` and a
`manifest_paths()` walk, mirroring `check-partition-edges.py`'s derivation —
never a literal. `fact_partitions()` and `amended_fact_ids()` now read every
matching manifest, with cross-manifest disagreement reported as an error
(same discipline as the existing nursery/split-policy disagreement check).

With the loader fixed, the gate correctly turns red on the real operation:
`authoritative-mathlib-nat-bit-constructor-family-v1` references four
`development` facts and no `train` fact. Verified this **is** case (a) from
ADR-1570's own measurement, re-confirmed here 2026-09-02: the live `train`
population across both manifests is 218 rows, 201 `proved`, exactly 17
`open` — 5 outcome-blind mutation fixtures, 2 divergence-blocked
(`Nat.fastFib`, `Squarefree`), and the 10 `natural-binomial-bounds` rows,
none reachable by the bounded refl/induction chain
`propose_bounded_induction` runs (`Nat.choose n k <= 2^n` is the contract's
own named non-example). The producer was authored in August against a
different (train) family and was not touched by the flywheel-3 lane. Added a
reviewed `GRANDFATHERED_OPERATIONS` entry (ADR-1570 as authority) with both
re-derived properties holding (all four facts `proved`, all four pin
`checker_operation.id` over this exact operation) — gate now passes with
`grandfathered_operations=2`.

Added `test_development_fact_in_extension_manifest_is_seen` (pins the
ADR-1570 defect: a dev-only operation touching only an extension-manifest
fact must still be caught) and `test_unrelated_manifest_shaped_file_is_not_
read` (a decoy `nursery-notes-v1.json`-shaped file must not be treated as a
manifest, matching `check-partition-edges.py`'s own control). All 17 tests in
`test_development_partition.py` pass. Mutation control added to
`scripts/tests/mutation_controls.py`'s `development-partition` entry:
reverting `MANIFEST_GLOBS` to `("nursery-v1.json",)` kills exactly
`test_development_fact_in_extension_manifest_is_seen` and nothing else, run
in the isolated scratch copy `mutation_controls.py` always uses.

**Fix 2.** `scripts/tests/test_check_autogenesis_holdout_isolation.py`'s
`test_the_committed_repository_passes` pinned a literal `held_out=206`
against a live count of 226 (draw 19, `882ae1a52`) — red on `main` before
this lane touched it. Replaced the literal with `committed_held_out_ids()`
(module-level, independent JSON walk of the two committed manifests, never
through `guard.held_out_facts()` itself) so the expected count is re-derived
at test time; kept a floor (`assertGreater(..., 0)`) for the "population is
not empty" half and an equality between the two independently-derived
numbers for the "gate counted right" half. Trimmed the ~140-line manual
move-by-move history comment (superseded; preserved in git blame) to a short
note on what changed and why the discipline it protected is not lost — those
checks live in `check-partition-edges.py`, `check-holdout-adjacency.py`,
`check-holdout-closed-evaluation.py`, and the amendment ledger, each still
gated separately. Added `test_the_held_out_count_moves_when_a_manifest_
gains_a_row`, which drives the SAME fixture to a different count and checks
the gate's output moves with it, so the re-derivation cannot be quietly
frozen. All 30 tests in the suite pass.

**Partition gates re-run, all green:** `check-development-partition.py`
(train=17 development=24 held-out=216, `grandfathered_operations=2`, PASS),
`check-autogenesis-holdout-isolation.py` (held_out=226, PASS),
`check-partition-edges.py --baseline` (crossing=51 amended=51 violations=0,
PASS), `check-holdout-adjacency.py` (22 families, 0 refused), `check-holdout-
closed-evaluation.py` (held_out=226, violations=0, PASS),
`check-autogenesis-holdout-contamination.py` (held_out=226, contaminated=0,
CLEAN), `check-dispatchable-frontier.py` (non-empty, witnessed).
`check-control-registration.sh` exits 0 (52/52 control scripts registered, 0
python orphans). `validate-facts.py`: 2682 facts, 0 errors, unaffected.

Did not run: no `cargo` gate (none expected for this Python-only change; not
touched). Did not push (not requested).

<!-- plan-section: landed-changes -->

| 2026-09-02 | dev-partition-all-manifests | opened the lane; status stub before any work |
| 2026-09-02 | dev-partition-all-manifests | `check-development-partition.py` reads every `nursery-v1.json` + `nursery-v*-extension.json` manifest, not `nursery-v1.json` alone (ADR-1570 defect) |
| 2026-09-02 | dev-partition-all-manifests | grandfathered `authoritative-mathlib-nat-bit-constructor-family-v1` (ADR-1570 authority, both re-derived properties hold); gate PASSes with the fixed loader |
| 2026-09-02 | dev-partition-all-manifests | two new tests + one mutation control pin the multi-manifest read in `test_development_partition.py` / `mutation_controls.py` |
| 2026-09-02 | dev-partition-all-manifests | `test_check_autogenesis_holdout_isolation.py`'s pinned `held_out=206` replaced with a re-derived count (`committed_held_out_ids`) plus a floor and a live-movement test |
