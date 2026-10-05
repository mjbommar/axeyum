# Lane: contracts-test-heldout-drift — fix the stale held-out-overlap literal in the producer-contracts test

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, contracts-test-heldout-drift, 2026-09-03).**
`scripts/tests/test_validate_producer_contracts.py` was red on `main`:
`KNOWN_HELD_OUT_SHAPE_MATCHES`, a hand-maintained literal id list, did not
move when `nat-coprime-family-v1`'s held-out shape overlap grew by a second
row (`omega-1`/`ebddccf27`, ADR-1561 draw 19) — the "test named 'every X'
must derive X from the authority" defect from
`docs/contributor-guide/evidence-and-checker-discipline.md`.

Fixed by derivation, not by extending the literal. `scripts/validate-
producer-contracts.py` gained guard (d): every held-out fact a contract's
shape predicate currently matches (re-derived live from every
`artifacts/autogenesis/nursery*.json` manifest and the fact ledger, never
from a literal) must carry a dated, reasoned entry in that contract's new
`sizing.held_out_overlap_reviewed`, keyed by a salted digest of the fact id
(`digest_held_out_fact_id`, ADR-1550's redaction pattern) — never by the id
itself, so the guard's own error output, the schema, the test file and this
status doc never name a held-out id. `artifacts/ontology/producer-
contract.schema.json` documents the two new optional `sizing` fields.
`artifacts/autogenesis/producer-contracts/nat-coprime-family-v1.json` now
carries a minted salt and two reviewed entries (both current overlaps).

`scripts/tests/test_validate_producer_contracts.py`: removed
`KNOWN_HELD_OUT_SHAPE_MATCHES` entirely; the class's main test now calls the
same live-derivation functions the validator's guard (d) calls
(`held_out_shape_matches`, `digest_held_out_fact_id`) and asserts the
property directly instead of diffing against a list. Added
`test_unclaimed_held_out_shape_overlap_needs_a_reviewed_digest`: a synthetic
fixture where a shape matches a held-out fact never named in
`matched_open_ready_fact_ids` and carries no review entry — confirms
`validate_contract` rejects it, confirms a correctly salted/digested review
entry clears it, and confirms a digest computed under the WRONG salt does
NOT clear it (so the guard verifies the digest, not merely list
non-emptiness). Also redesigned `test_the_v1_only_reader_is_the_one_that_
misses_it` to derive its subject (a contract whose held-out overlap depends
on a non-`nursery-v1.json` manifest) at test time rather than reading it out
of the removed literal.

Reproduced before fixing: `AssertionError: Lists differ` naming the new
overlap fact id, which is why the fix routes everything through salted
digests from here on — the failing assertion itself was the last place in
this codebase's history that a held-out id appeared in a test's own output.

Verified: `python3 scripts/tests/test_validate_producer_contracts.py` — 27
tests, was 26 (added one control), all green.
`python3 scripts/validate-producer-contracts.py` — exit 0, `contracts=4`.
`scripts/check-control-registration.sh` — exit 0, `orphans=0`.
`python3 scripts/check-autogenesis-holdout-isolation.py` — `references=0`,
`verdict=PASS`, unaffected (digests, not ids, land in the contract file).
`python3 scripts/tests/mutation_controls.py producer-contracts` — 9 guards,
all single kills; the new guard ("a held-out shape overlap with no reviewed
digest must be rejected") kills exactly
`test_unclaimed_held_out_shape_overlap_needs_a_reviewed_digest` and nothing
else. `--check-anchors` confirms no ambiguous/unmatched anchor. Mutation ran
through `mutation_controls.py`'s own copy-to-scratch isolation, not in the
shared worktree.
`scripts/check-merge-hygiene.sh` — ran after this fix; also caught a
pre-existing, unrelated `frontier-shape-census.py --check` drift (the
committed digest lagged the ledger state after the earlier merge) and
`gen-plan.py --check`; both regenerated and committed alongside this lane's
status update, per standing practice for a lane that runs the merge-hygiene
gate last.

No cargo run (none expected for this task; no `.rs` file touched). Did not
push.

<!-- plan-section: landed-changes -->

| 2026-09-03 | contracts-test-heldout-drift | fixed the stale `KNOWN_HELD_OUT_SHAPE_MATCHES` literal: producer-contract sizing blocks now carry a salted-digest `held_out_overlap_reviewed` field, validated live against every nursery manifest, never a hardcoded id list |
