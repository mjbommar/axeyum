# Notes: 137-decline-feedback

Detail moved out of [`../status/137-decline-feedback.md`](../status/137-decline-feedback.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
