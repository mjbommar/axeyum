# Lane: decline-feedback — declines become selector input

<!-- plan-section: lane-status -->

**Closed the loop doc 290 exposed** (`DONE`, decline-feedback, 2026-08-27).
Verified first: on the merged tree, `scripts/fact-frontier.py --json` still
selected `F:ml430-int-add-modeq-left-ee732b5b` (`admissible_count: 27`) even
though the fact's own decline artifact
(`artifacts/autogenesis/mathlib-int-add-modeq-left-decline-v1.json`) already
recorded a real, typed producer decline (`TerminalNotClosed`) against it —
nothing read the decline back, so the selector would loop on it forever.

**Convention (doc
[291](../../autogenesis/291-decline-feedback-loop.md)):** a contract-driven
decline is identified structurally (top-level `contract` + `fact_id`,
`producer.result == "declined"`), distinguishing it from the eleven
pre-ADR-0602 decline files with no such shape. Extended the one existing
instance with `contract_sha256` (purely additive) — the sha256 of the
contract's full canonical JSON at decline time, which is the re-dispatch key:
a decline is live only while it matches the contract's *current* digest, so
editing a contract's recipe/shape automatically re-opens everything it
declined, with no manual clearing.

**`scripts/validate-producer-contract-declines.py`** (new; 25 unit tests,
8 mutation guards, all killed — `python3 scripts/tests/mutation_controls.py
producer-contract-declines`) enforces the failure mode named in the brief:
*a decline artifact must not become a cheap way to make the selector shut up
about a fact forever.* `decline_reason` must be a bare typed identifier
(`^[A-Z][A-Za-z0-9]*$`, the shape of a Rust `DeclineReason` enum variant),
never free text; `fact_id`/`contract` must resolve to real committed
artifacts; `producer.result` must be exactly `"declined"`; `producer.tool` /
`decline_message` must be non-empty.

Detail moved to [`../notes/137-decline-feedback.md`](../notes/137-decline-feedback.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `e0c96569e` | Contract-decline convention (doc 291): `contract_sha256` re-dispatch key added to the seed decline artifact; new `scripts/validate-producer-contract-declines.py` (25 tests). |
| 2026-08-27 | `96e40ce3d` | `scripts/fact-frontier.py` reads decline artifacts as selector input: live-decline computation, three-population diagnostics, `declined_fact_ids`. Selection moves off the declined fact. |
| 2026-08-27 | `cdc10b413` | Wired the decline validator into `scripts/check.sh`, `justfile`, and an 8-guard mutation suite in `scripts/tests/mutation_controls.py` (all killed). |
