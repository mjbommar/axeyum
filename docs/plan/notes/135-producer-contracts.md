# Notes: 135-producer-contracts

Detail moved out of [`../status/135-producer-contracts.md`](../status/135-producer-contracts.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Landed:**
- `artifacts/ontology/producer-contract.schema.json` — no `proved`/
  `epistemic_status` field exists anywhere in the schema; the false assertion
  is unrepresentable, not merely forbidden.
- `scripts/validate-producer-contracts.py` — schema-valid; every non-example
  resolves to a REAL fact and is checked to FAIL its shape predicate BY
  EXECUTION; rejects a predicate matching every open fact (the vacuous-matcher
  defect); rejects a shape narrowed only by language/fragment. 15 unit tests,
  plus a 5-guard mutation-testing entry in `scripts/tests/mutation_controls.py`
  (`producer-contracts`): 5 killed, 0 survived, 0 unmeasured.
- Two seed contracts, both `kernel-lane`, both genuinely general, both
  checked against `nursery-v1.json` — every match is `train`/`development`,
  zero `held-out`:
  - `producer-contract-int-modeq-family-v1` (Int modular-congruence facts,
    `statement_contains "[ZMOD "` — generalizes past doc 288's four named
    facts and past the `Int.ModEq.*` naming convention to the free-function
    spelling too; 13 open, 6 already proved, all `train`).
  - `producer-contract-nat-coprime-family-v1` (substituted for ADR-0602's
    CReal/Complex example, since zero open CReal/Complex facts exist today —
    all this week's ~30 new ones are already `proved`; `Nat.Coprime` family
    instead, `statement_contains "Coprime"` scoped by title prefix to exclude
    the outcome-blind mutation fixtures in the same namespace; 22 open, 1
    already proved, mostly `development`).
- `scripts/fact-frontier.py` — admissibility redefined as dependency-ready ×
  (registered operation OR matched producer contract with a capable route) ×
  no gate-review issues; `route_capability()` reports `kernel-lane` always
  capable, `cas-bridge`/`import` gated on sibling-lane artifacts that don't
  exist in this tree yet (absent-tolerant, never raises); the 6 no-route
  facts are named in a new `diagnostics.no_route_ready_fact_ids` key and can
  never become admissible via either path. All 8 existing
  `test_fact_frontier.py` tests pass **unmodified**; 7 new tests added to the
  same file.
- `docs/autogenesis/289-producer-contract-admissibility.md` — full writeup,
  including the `contracts=None` deliberate-asymmetry design decision that
  made "8 tests unmodified" and "admissible > 0 on the real ledger"
  simultaneously satisfiable (three of the eight tests build over the FULL
  real ledger with only the operation registry reduced to a controlled
  subset; auto-loading real contracts the same way the registry auto-loads
  would leak ~27 other real admissible facts into those tests with no
  argument to control for it).

**Measured result:** `python3 scripts/fact-frontier.py --json` now reports
`admissible_count: 27` (`admissible_via_contract_count: 27`,
`admissible_via_operation_count: 0`), `selected_fact_id:
F:ml430-int-add-modeq-left-ee732b5b` — genuinely still `epistemic_status:
"open"`, no receipt fabricated. `--output`/`--verify` round-trip
self-consistently. `check-autogenesis-holdout-isolation.py` still passes
(`held_out=37|references=0|verdict=PASS`).

**Registered in `scripts/check.sh`** (`autogenesis-producer-contracts`,
`autogenesis-producer-contracts-tests`) and **`justfile`**
(`autogenesis-producer-contracts` target, plus wired into
`autogenesis-operations`'s neighbourhood and `generated-trackers`).

**Did not touch:** `scripts/validate-facts.py`, `scripts/gen-import-backlog.py`,
`artifacts/import-backlog.json` (an adr601-impl lane's), the operation
registry's validator/instances beyond reading, `artifacts/facts/`,
`docs/curriculum/curriculum.toml`, `crates/`, or `python/axeyum/agent/` — all
out of scope per the brief.

**Next.** 98 of the 125 `proof-route-only` ready facts still have no
contract authored for their shape (`diagnostics.unmatched_by_route_class.
proof-route-only`). A third seed contract over another real, general shape in
that pool (e.g. the `gcd`/`log`/`prime`/`factorial` families visible in the
same `ml430-*` import batch) would grow `admissible_count` further without
touching the receipt system. Separately, `cas-bridge`/`import` route
capability is 0 today purely because neither sibling artifact exists in this
tree yet; once either lands, contracts declaring that route become live with
no further `fact-frontier.py` change needed.
