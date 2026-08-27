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

**`scripts/fact-frontier.py`** now loads and validates every decline
(`load_decline_artifacts`, mirroring `load_producer_contracts`), computes
live `(fact, contract)` pairs (`live_declined_pairs`), and a live decline
removes exactly that pair from admission via the CONTRACT path only (never
the operation-receipt path, never widening anything). `declines=None`
defaults to empty, asymmetric with auto-loading, matching the existing
`contracts=None` convention — all 15 pre-existing `test_fact_frontier.py`
tests pass **unmodified**.

**Three populations, not two**, in `diagnostics`: `shape_matched_count`
(what `admissible_count` used to measure), `declined_count` (previously
invisible), `admissible_count`/`admissible_via_contract_count` (now
correctly excludes declined pairs). `declined_by_contract` gives per-contract
counts; `selection.declined_fact_ids` lists declined facts visibly (doc
288's `no_route_ready_fact_ids` precedent — never silently dropped).

**New selection on the current tree**, verbatim from `--json`:

```
selected_fact_id: F:ml430-int-add-modeq-right-e58108ee
admissible_count: 26          (was 27)
shape_matched_count: 27
declined_count: 1
declined_by_contract: {'producer-contract-int-modeq-family-v1': 1}
declined_fact_ids: ['F:ml430-int-add-modeq-left-ee732b5b']
```

A different `Int.ModEq` family member, exactly as the task predicted — the
loop moved on rather than re-selecting the same declined fact.

**Re-dispatch verified both directions** (`test_live_decline_removes_
admissibility_and_reports_declined`, `test_stale_decline_against_a_changed_
contract_does_not_suppress`): a decline whose `contract_sha256` matches the
contract's current digest suppresses; a decline with any other digest
(simulating an edited contract) does not, and the fact stays admissible.

**Verified:** `python3 scripts/validate-facts.py` (unchanged distribution),
`python3 scripts/validate-producer-contracts.py` (2 contracts, unchanged),
`python3 scripts/check-autogenesis-holdout-isolation.py`
(`held_out=37|settled=0|verdict=PASS`, unchanged), `python3 scripts/fact-
frontier.py --verify` round-trips the freshly generated artifact,
`python3 -m unittest scripts.tests.test_fact_frontier` (21 tests, 6 new),
`python3 -m unittest scripts.tests.test_validate_producer_contract_declines`
(25 tests).

**Explicitly not attempted**, per the brief: no refinement of the shape
predicates themselves (a finer-grained shape distinguishing
combinator-over-hypotheses from derive-a-new-identity facts *at match time*
is real future work, a producer-capability question rather than a
feedback-loop question — conflating the two here would do neither carefully).

**Did not touch:** `artifacts/facts/`, either producer contract instance's
shape/recipe, `artifacts/autogenesis/operations.json`, anything under
`crates/`, `python/axeyum/agent/`.

<!-- plan-section: landed-changes -->

| 2026-08-27 | `e0c96569e` | Contract-decline convention (doc 291): `contract_sha256` re-dispatch key added to the seed decline artifact; new `scripts/validate-producer-contract-declines.py` (25 tests). |
| 2026-08-27 | `96e40ce3d` | `scripts/fact-frontier.py` reads decline artifacts as selector input: live-decline computation, three-population diagnostics, `declined_fact_ids`. Selection moves off the declined fact. |
| 2026-08-27 | `cdc10b413` | Wired the decline validator into `scripts/check.sh`, `justfile`, and an 8-guard mutation suite in `scripts/tests/mutation_controls.py` (all killed). |
