# 289 — Producer contracts: `admissible` moves off zero without fabricating a receipt

Date: 2026-08-27

## Task

Implement ADR-0602: the prospective producer-contract artifact and
contract-based admissibility, closing the gap doc
[`288`](288-admission-precedes-registration.md) diagnosed -- `admissible: 0`
over 132 dependency-ready facts, because the operation registry's
`ADMISSION_CONTRACTS` requires `epistemic_status: "proved"` on every arm and
cannot represent "we could attempt this open fact" without asserting a proof
that does not exist.

## What landed

**Schema.** `artifacts/ontology/producer-contract.schema.json`. A contract is
a capability claim only: `route` (`kernel-lane`/`cas-bridge`/`import`), a
`recipe` (prose description + optional code reference), a `shape` (the
executable predicate), and `non_examples` (>=1 real fact id the predicate
provably does not match). **There is no `proved` or `epistemic_status` field
anywhere in the schema**, and `additionalProperties: false` at every level
makes adding one a schema violation, not a reviewable choice -- verified by a
mutation-tested guard (`test_no_proved_or_epistemic_status_field_is_representable`)
and, structurally, by the schema itself never declaring the property.

**Shape predicate design.** Five optional fields, ANDed: `formal_language`,
`fragments` (both required, arrays), and at least one of `title_prefix`,
`statement_contains`, `id_prefix` (validator-enforced -- language+fragment
alone is "almost the whole ledger", not a shape). Matching is executed by
`shape_matches()` in `scripts/validate-producer-contracts.py`, imported by
`scripts/fact-frontier.py` via the same `importlib`-loaded-module pattern the
file already uses for the operation validator, so the two can never silently
disagree about what a shape means.

**Validator.** `scripts/validate-producer-contracts.py`:
- schema-valid (hand-rolled structural checks, matching this repository's
  no-`jsonschema`-dependency convention for `validate-facts.py` and
  `validate-autogenesis-operations.py`);
- every `non_example.fact_id` resolves against the REAL `artifacts/facts/`
  ledger and is checked to FAIL the shape predicate BY EXECUTION -- never
  trusted from its `reason` prose;
- rejects a shape predicate that matches every open fact in the ledger (the
  vacuous-matcher defect, one arrow upstream of the operation registry it was
  meant to unblock);
- rejects a shape narrowed only by `formal_language`/`fragments`.

15 unit tests (`scripts/tests/test_validate_producer_contracts.py`), plus a
mutation-testing entry in `scripts/tests/mutation_controls.py` under
`producer-contracts`: **5 guards, 5 killed, 0 survived, 0 unmeasured**
(`python3 scripts/tests/mutation_controls.py producer-contracts`, run against
a scratch copy per the harness's own design -- never against the shared
checkout).

**Admissibility redefinition, in `scripts/fact-frontier.py`.**
`build_machine_frontier` now computes, per ready fact, both `registered_
operation_ids` (unchanged, doc 288's receipt path) and `matched_producer_
contract_ids` (new). An entry is admissible when EITHER path succeeds
(exactly one operation, or exactly one matched contract whose route is
capable) AND the fragment has a supported route AND gate review is clean.
`route_capability()` reports `kernel-lane` always capable, `cas-bridge` and
`import` gated on sibling-lane artifacts (`artifacts/autogenesis/
cas-bridge-manifest.json`, `artifacts/import-backlog.json`) that do not exist
in this tree yet -- checked by existence, absent-tolerant, never raising, so
this file stays buildable independently of when either sibling lane lands.
The 6 no-route facts are reported by name in a new `diagnostics.
no_route_ready_fact_ids` key and can never become admissible via either path
(`route_class == "no-route"` is a hard gate on `is_admissible`, independent of
producer).

**A subtlety that needed its own design decision: `contracts=None` means NO
contracts, deliberately asymmetric with `registry=None` (which auto-loads the
real operation registry).** The obvious symmetric choice -- auto-load real
contracts whenever omitted, exactly like the registry -- breaks 3 of the 8
existing `test_fact_frontier.py` tests, none of which the task permits
touching. Those tests call `build_machine_frontier(frontier.load(), registry)`
-- the REAL, full ledger, with only the operation registry reduced to a
controlled subset -- specifically to isolate one operation's effect from every
other real one. Real seed contracts auto-loading in would leak in ~27 other
real admissible facts with no argument in those calls to reduce, and
`admissible[0]` (lexicographic) would pick one of THOSE over the test's
intended target. So `contracts=None` means empty; `main()` (the CLI) and
`verify_machine_frontier` (self-consistency checking) both explicitly call
`load_producer_contracts()` to get the real, current set -- and that loader
validates non-examples and the vacuous-match guard against the REAL committed
ledger unconditionally, never against whatever `facts` dict a particular
`build_machine_frontier` call happens to be iterating over, for the same
reason (a synthetic 3-fact test ledger must not make a real, valid contract
fail validation because its non-example "doesn't resolve" in that small dict).

All 8 existing tests pass **unmodified**; 7 new tests were added to the same
file (`ProducerContractAdmissibilityTests`, `RealSeedProducerContractTests`),
exercising: a matched contract with a capable route is admissible; an
incapable route (`cas-bridge`, no manifest) blocks it; two matching contracts
are `ambiguous-producer-contract`, not admissible; a `no-route` fragment is
never admissible via contract regardless of match; `contracts=None` truly
means none; and the real seed contracts move `admissible_count` off zero
end-to-end over the live ledger.

## Seed contracts

Both `kernel-lane`, both genuinely general (`shape` matches a family, not one
fact), both checked against `nursery-v1.json`: **every current match is
`train` or `development`, none `held-out`** (verified two ways: a dedicated
unit test, `SeedContractHoldoutIsolationTests.test_seed_contracts_match_no_
held_out_fact`, and `scripts/check-autogenesis-holdout-isolation.py` itself,
which passed with `references=0` after these files landed under
`artifacts/autogenesis/`).

- **`producer-contract-int-modeq-family-v1`** -- doc 288 names four Int.ModEq
  facts as the best next candidate for a genuinely general operation
  (`F:ml430-int-modeq-add-left-6e17c69a`, `-neg-f649f6c5`, `-of-dvd-b9c41fce`,
  `-sub-3148f130`). The shape generalizes past those four and past the
  `Int.ModEq.*` naming convention specifically: it matches on `fragment ==
  "Int"` and `statement_contains "[ZMOD "` (the modular-congruence notation
  itself), which also covers the free-function spelling (`Int.add_modEq_left`,
  `Int.neg_modEq_neg`, ...) that doc 288's naming-based framing would have
  missed. 19 facts match total (13 open, 6 already `proved`), all `train`.
  Non-examples: `F:ml430-int-fib-add-181b6a2c` (same import shape, no `[ZMOD `
  token) and `F:ml430-nat-modeq-add-left-e83f0700` (same lemma shape, wrong
  fragment and `[MOD ` not `[ZMOD `).
- **`producer-contract-nat-coprime-family-v1`** -- ADR-0602's brief suggested
  scoping the second contract to "the CReal/Complex families this week's work
  covers"; measured 2026-08-27, there are currently **zero open CReal/Complex
  facts** (all 176 open facts are `Nat` (141), `Int` (31), `none` (6), or
  `QF_FP` (1) -- this week's ~30 new CReal/Complex facts are all already
  `proved`). Substituted a different real, general shape from the same
  `proof-route-only` ready pool: `fragment == "Nat"` and `statement_contains
  "Coprime"`, scoped to `title_prefix "Mathlib v4.30 source proposition "` to
  structurally exclude the outcome-blind mutation fixtures in the same
  namespace (`Nat.Coprime 0 0` appears in a deliberately polarity-reversed
  mutation of `Nat.not_coprime_zero_zero`; the title prefix, not an id
  denylist, is what excludes it). 23 facts match (22 open, 1 `proved`), 22
  `development` / 1 `train`. Non-examples: `F:ml430-nat-modeq-add-left-e83f0700`
  (same fragment, wrong family) and the mutation fixture itself
  (`F:ml430-mutation-c20db9b4c60b816ce738bdf2`, matches on statement content
  alone but excluded by the title-prefix constraint).

## Measured result

```
$ python3 scripts/fact-frontier.py --json
  diagnostics.ready_count: 132
  diagnostics.admissible_count: 27
  diagnostics.admissible_via_operation_count: 0
  diagnostics.admissible_via_contract_count: 27
  diagnostics.unregistered_by_route_class: {decidable: 1, no-route: 6, proof-route-only: 125}
  diagnostics.unmatched_by_route_class: {decidable: 1, no-route: 6, proof-route-only: 98}
  diagnostics.no_route_ready_fact_ids: [F:collatz-reaches-one, F:continuum-hypothesis-independent,
    F:excluded-middle-not-intuitionistic, F:fermat-last-theorem, F:fol-validity-undecidable,
    F:godel-first-incompleteness]
  selection.outcome: selected
  selection.selected_fact_id: F:ml430-int-add-modeq-left-ee732b5b
  selection.admissible_fact_ids: 27 facts (12 via producer-contract-int-modeq-family-v1,
    15 via producer-contract-nat-coprime-family-v1)
```

The selected entry: `route_class: proof-route-only`, `registered_operation_
ids: []`, `matched_producer_contract_ids: ["producer-contract-int-modeq-
family-v1"]`, `producer_contract_route: "kernel-lane"`, `producer_contract_
route_capable: true`, `epistemic_status: "open"` -- genuinely still open, no
receipt fabricated. `no_route_ready_fact_ids` names all 6 no-route facts and
none appear in `admissible_fact_ids` (asserted by a dedicated test).

27 < 125: the 98 remaining `proof-route-only` ready facts have no contract
authored for their shape yet (`unmatched_by_route_class.proof-route-only:
98`), which is the honest state of the world -- a contract is a claim someone
has to write and stand behind, not something that appears because the schema
exists.

## What this does NOT do, and why

- **No fact's `epistemic_status` changed.** A contract licenses *dispatch*
  (per ADR-0602: "a selection is an instruction to dispatch... only the
  resulting receipt... ever touches the operation registry"), never admission.
  Nobody proved anything in this session; `validate-autogenesis-operations.py`
  and `artifacts/autogenesis/operations.json` are untouched.
- **`cas-bridge` and `import` routes report `False`** for capability today
  (no manifest, no backlog artifact in this tree) -- correct, since neither
  sibling lane had landed its artifact as of this session, and absent-tolerant
  checking means this file needed no coordination with either to build and
  land independently.
- **Did not touch `artifacts/facts/`, `docs/curriculum/curriculum.toml`,
  `crates/`, or `python/axeyum/agent/`** -- out of scope per the brief.

## Verification run

```
python3 scripts/validate-producer-contracts.py            -> PRODUCER_CONTRACTS_OK|contracts=2
python3 -m unittest scripts.tests.test_validate_producer_contracts   -> 15 passed
python3 scripts/tests/mutation_controls.py producer-contracts        -> 5 guards, 5 killed, 0 survived
python3 -m unittest scripts.tests.test_fact_frontier                 -> 15 passed (8 original unmodified + 7 new)
python3 scripts/validate-autogenesis-operations.py                   -> unchanged, 27 operations
python3 scripts/check-autogenesis-holdout-isolation.py                -> held_out=37|references=0|verdict=PASS
python3 scripts/fact-frontier.py --output /tmp/f.json && \
python3 scripts/fact-frontier.py --verify /tmp/f.json                -> FACT_FRONTIER_OK (round-trips)
```
