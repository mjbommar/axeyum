# Lane: flywheel-2 — batched contract dispatch over all admissible facts

<!-- plan-section: lane-status -->

**`DONE` (2026-08-27).** Turn one (`flywheel-1`, status 136) processed
one fact end to end (`F:ml430-int-add-modeq-left-ee732b5b`, honest decline).
This lane's job is to amortize the per-dispatch setup (s5 session, pin
verification, adapter boilerplate) across every fact `scripts/fact-frontier.py
--json` currently reports admissible, rather than repeating it 26 times.

**Before state** (`scripts/fact-frontier.py --json`, verified against the
merged tree carrying `scripts/validate-producer-contract-declines.py` and doc
291): `admissible_count: 26` (`admissible_via_contract_count: 26`,
`admissible_via_operation_count: 0`), `declined_count: 1`
(`producer-contract-int-modeq-family-v1`), `selected_fact_id:
F:ml430-int-add-modeq-right-e58108ee`. 11 facts match
`producer-contract-int-modeq-family-v1` (`fragment: Int`,
`statement_contains: "[ZMOD "`), 15 match `producer-contract-nat-coprime-family-v1`
(`fragment: Nat`, `statement_contains: "Coprime"`). Partition check against
`artifacts/autogenesis/nursery-v1.json`: all 26 are `train` or `development`;
none held-out (ADR-0542 respected).

Pins verified once on s5: mathlib4 `c5ea00351c28e24afc9f0f84379aa41082b1188f`,
lean4export `a3e35a584f59b390667db7269cd37fca8575e4bf` — both match the
manifest.

`crates/axeyum-lean-import`'s two dispatch tools
(`statement_adapter_import`, `modeq_family_operation`) built locally
(`cargo build -p axeyum-lean-import --examples`, ~30s, clean) so the batch
does not pay a full workspace build per fact.

Detail moved to [`../notes/138-flywheel-2-batch-dispatch.md`](../notes/138-flywheel-2-batch-dispatch.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `PENDING` | Batch dispatch over all 26 currently admissible facts (11 `int-modeq-family-v1`, 15 `nat-coprime-family-v1`). Result: 26 honest declines, 0 proofs — 11 clean-import `TerminalNotClosed` (int-modeq, matching turn one's mechanism), 15 import-stage `TrustedDeclaration` (nat-coprime, a new finding this batch's own predictions missed). After state: admissible_count 0, declined_count 27, selection refused-no-admissible-candidate. All validators green. |
