# 296 — A general kernel-lane execution driver: receipts for hand-authored proofs

Date: 2026-08-27
Lane: kernel-receipt

## Task

Doc 293 proved five `Int.ModEq` theorems directly against the kernel
(`crates/axeyum-lean-kernel/src/int_prelude/modeq_family.rs`), with no
producer/checker/executor pipeline component running at all, and closed the
five facts it targets. It then tried to register a retrospective operation
receipt (ADR-0602) and was genuinely blocked: `validate-autogenesis-
operations.py`'s `EXECUTION_DRIVERS` was a closed set of ten, of which eight
are `axeyum-lean-import/*` (pipelined: adapter -> export -> import ->
checker) and two are named for one-off episodes
(`nat-zero-add-induction-v1`, `nat-mul-one-episode-apply-v1`). None of them
describes "an agent read a Mathlib statement and hand-wrote a new kernel
proof directly against `Kernel::add_declaration`." Per doc 288's
measurement, 125 of 132 dependency-ready facts are exactly this
`proof-route-only` shape, so the receipt system was blind to the dominant
route in this project.

This lane's job was to close that gap without editing the fact ledger, the
producer-contract instances, or anything under `crates/`.

## The driver: `axeyum-lean-kernel/authored-declaration-v1`

Added to `EXECUTION_DRIVERS` in `scripts/validate-autogenesis-operations.py`,
alongside a new field-set case in `validate_executor` and a consistency
branch in `validate_registry` (mirroring `modeq-family-multi-target-v1`'s
Int/Nat-agnostic fragment set, since this driver is not tied to any one
fragment). Its executor fields, beyond the shared `driver` /
`implementation` / `input_fact_id` / `timeout_seconds` /
`expected_evidence_label`:

| field | purpose |
|---|---|
| `additional_fact_ids` | the rest of the facts this one operation covers, alongside `input_fact_id` |
| `declaration_source` | the repo-relative Rust file containing the declaration(s), inside `crates/axeyum-lean-kernel/` |
| `test_path` | the repo-relative test file, inside `crates/axeyum-lean-kernel/` |
| `verifying_tests` | test function names that must exist in `test_path` |
| `targets` | one `{fact_id, declaration}` object per covered fact, in `input_fact_id`-then-`additional_fact_ids` order |

Every field is chosen to be **re-checkable**, not narrative:

- `declaration_source`/`test_path` must exist and be inside
  `crates/axeyum-lean-kernel/` — this driver names kernel-lane work, not an
  import or a bench artifact, and the validator reads the crate boundary
  directly from the path rather than trusting a label.
- Each `verifying_tests` entry must appear as `fn <name>(` in `test_path`'s
  actual text (`re.search`, checked at validation time) — a receipt naming a
  test that does not exist there fails, rather than a name that could drift
  silently out of sync with the source.
- Each `targets[].declaration` must (a) match a qualified-Lean-name shape
  (`LEAN_DECLARATION_RE`, e.g. `Int.add_modEq_left`), (b) be bound to exactly
  one fact within the operation, and — the check that actually makes this
  driver mean something — (c) **appear literally inside
  `declaration_source`'s text**. A receipt naming a declaration the source
  file never mentions is exactly the forgery this driver exists to reject,
  and it is checked by reading the file, not by trusting the JSON.
- `targets` must bind fact ids in exactly `input_fact_id` +
  `additional_fact_ids` order (wired into the same generic multi-target
  binding check `bounded-induction-multi-target-v1` and
  `modeq-family-multi-target-v1` already use), so `applicability.fact_ids`
  cannot silently diverge from what the executor actually claims.

This is deliberately the same shape of evidence the five closed facts
already carry in `artifacts/facts/`: a statement pin, an axiom-footprint
check, and a concrete-correctness check, all as named Rust test functions
(`the_modeq_ledger_rows_are_stated_without_a_positivity_hypothesis`,
`derived_laws_have_no_axiom_footprint`,
`every_int_declaration_is_checked_and_axiom_free`,
`add_modeq_family_computes_at_concrete_values`). The receipt does not
introduce a new claim; it points at the evidence that already exists.

## Registration: doc 293's five closures as ONE operation

`authoritative-kernel-int-modeq-shift-family-v1` in
`artifacts/autogenesis/operations.json`, naming all five facts in
`applicability.fact_ids` and `executor.targets`:

- `F:ml430-int-add-modeq-left-ee732b5b` -> `Int.add_modEq_left`
- `F:ml430-int-add-modeq-right-e58108ee` -> `Int.add_modEq_right`
- `F:ml430-int-mod-modeq-6bec7847` -> `Int.mod_modEq`
- `F:ml430-int-modulus-modeq-zero-5b57a898` -> `Int.modulus_modEq_zero`
- `F:ml430-int-modeq-sub-3148f130` -> `Int.modEq_sub`

Per CLAUDE.md's standing lesson from doc 228 ("an operation registry where
every entry names one target is a dispatch table, not a producer"), this is
registered as a SINGLE operation naming all five, not five capsule-shaped
operations. `python3 scripts/validate-autogenesis-operations.py`:
`AUTOGENESIS_OPERATIONS_OK|operations=28`.

### Does the provenance ledger's generality counter see it?

Partially, and the split is worth stating precisely because the two
counters in `scripts/gen-production-provenance-ledger.py` answer different
questions:

- `multi_target_operations` (operations with `applicability.fact_ids` width
  > 1) reads `operations.json` alone and rose **3 -> 4** immediately upon
  registration — this counter cannot fail to see it, because it never looks
  at a fact.
- `facts_via_multi_target` (`generality[GENERAL]`, the actual headline
  metric) reads `fact.evidence[].checker_operation.id` and joins it back to
  the registry. Regenerating the ledger after this registration
  (`python3 scripts/gen-production-provenance-ledger.py`) shows
  `via_multi_target` unchanged in composition: it moved 11 -> 14 in this same
  regeneration, but the three new names in the "Facts:" list —
  `F:ml430-nat-add-modeq-left-e3b1fba9`, `F:ml430-nat-add-modeq-right-e2f11f21`,
  `F:ml430-nat-modulus-modeq-zero-fd9af096` — are Nat-fragment siblings
  already bound to the pre-existing `modeq-family-multi-target-v1` operation
  from work merged in independently of this lane. **None of doc 293's five
  Int facts appear in that list.**

The reason is structural, not a bug: this lane's scope explicitly excludes
`artifacts/facts/` ("the five are already closed and correct"), and the
join key is a fact's own `evidence[].checker_operation.id` — a field none of
the five facts' evidence rows currently carry (checked directly: all three
evidence rows on each of the five facts have `checker_operation: null`
today). So `operation_ids(fact)` returns empty for all five, `classify()`
labels them `NO_OP`, and the generality counter cannot credit this
registration until a lane that owns `artifacts/facts/` adds
`"checker_operation": {"id": "authoritative-kernel-int-modeq-shift-family-v1"}`
to one evidence row per fact. **This is not something this lane can fix
without violating its own scope boundary**, and it is worth flagging as the
natural next step for whichever lane next touches these five facts' evidence.

The regenerated ledger (`docs/plan/generated/production-provenance-ledger.md`)
is committed alongside this registration, since it is a generated view of
`operations.json` and `just check`/`check.sh` gate `--check` on it staying
fresh.

## Discrimination: proven both ways

`scripts/tests/test_validate_autogenesis_operations.py` gained ten new
tests: one confirming the committed five-fact registration validates and
that `gen-production-provenance-ledger.py`'s `operation_widths()` reports it
at width 5, and nine adversarial mutations of the committed registry proving
each individual guard fires — an absent declaration, a declaration bound to
two facts, a missing verifying test, a source file outside the kernel crate,
a malformed declaration name (three sub-cases), a repeated fact id, a
misordered `targets` list, an applicability/fact-id mismatch, and an
inconsistent admission/applicability tuple.

Eight mutation guards are registered in `scripts/tests/mutation_controls.py`
under `autogenesis-authored-declaration-driver`, run against
`scripts/validate-autogenesis-operations.py` directly (never the shared
checkout — the harness copies to a scratch tree). Each guard's mutation
kills exactly the one test written for it:

```
autogenesis-authored-declaration-driver: baseline green, 34 tests
  a declaration must appear in its claimed source file killed 1: ...rejects_a_declaration_absent_from_its_source
  one Lean declaration may not be bound to two facts killed 1: ...rejects_one_declaration_bound_twice
  a verifying test must exist as a fn in the named test file killed 1: ...rejects_a_missing_verifying_test
  declaration_source/test_path must stay inside the kernel crate killed 1: ...rejects_a_source_outside_the_kernel_crate
  a target declaration must be a qualified Lean name killed 3: ...rejects_a_malformed_declaration_name (x3, one test's subTest cases)
  no fact id may repeat across input_fact_id/additional_fact_ids killed 1: ...rejects_a_duplicate_fact_id
  targets must bind fact ids in input+additional order killed 1: ...rejects_target_order_mismatch
  this driver's applicability/admission must stay in its closed set killed 1: ...is_inconsistent_with_wrong_admission
```

**The first attempt at the last guard was wrong, and worth recording.**
Mutating the whole `elif executor["driver"] ==
"axeyum-lean-kernel/authored-declaration-v1":` branch away (to `elif
False:`) does not merely disable that branch's own check — it makes the
committed operation fall through to a LATER, stricter `elif` in the same
chain (the Nat-only `checked-theorem-receipt-v1`-style default), which then
rejects the base committed registry outright. That single mutation killed
**five** unrelated tests via this collateral fallthrough, exactly the
"checker that cannot fail" trap CLAUDE.md warns about, arriving from the
opposite direction — not a guard too weak to fail, but a mutation too broad
to be surgical. Fixed by mutating only the inner `if (...)` condition
(`if False and (...)`) so the branch is still selected and only its own
check is disabled; re-run showed exactly one death.

## ADR-0602 amendment

Appended (not rewritten) to
`docs/research/09-decisions/adr-0602-operations-are-receipts-dispatch-needs-producer-contracts.md`,
recording that receipts could previously only describe pipelined work, that
this general driver closes it, and that the `applicability.fact_ids`
breadth rule (doc 228) applies to it exactly as to any other operation.

## Also reported, not fixed: the `int-modeq-family-v1` contract's route label

Doc 293 already found this and this lane re-confirms it rather than
touching the contract file (out of scope per this lane's brief — "another
lane owns the contract instances"):
`artifacts/autogenesis/producer-contracts/int-modeq-family-v1.json` labels
its `route` as `kernel-lane`, but every operation ever registered against
its shape (`modeq-family-multi-target-v1`) is import-mediated: author a
Lean adapter, export via `lean4export`, import, then run
`propose_modeq_family`. Doc 293's five proofs are the first genuinely
kernel-lane closures in this family, and with a real kernel-lane driver now
existing (`authored-declaration-v1`), the mismatch is sharper than when doc
293 found it: the contract's label and its own recipe now disagree with
BOTH the driver vocabulary that exists (there is a real `kernel-lane`
driver) AND the only driver actually used against it (which is
import-mediated). Recommendation: either re-label
`int-modeq-family-v1`'s `route` to `import`, or add a sibling `kernel-lane`
contract that names `authored-declaration-v1` as its executor shape. Left
to whichever lane owns `artifacts/autogenesis/producer-contracts/`.

## Scope discipline

Touched: `scripts/validate-autogenesis-operations.py`,
`scripts/tests/test_validate_autogenesis_operations.py`,
`scripts/tests/mutation_controls.py`,
`artifacts/autogenesis/operations.json` (one new operation, no
amendments/deletions to existing entries),
`docs/plan/generated/production-provenance-ledger.md` (regenerated, since
`operations.json` is its sole non-fact input and the aggregate gate checks
it stays fresh), this doc, and the ADR-0602 amendment.

Not touched: `artifacts/facts/`, any producer-contract instance,
`scripts/validate-producer-contracts.py` /
`validate-producer-contract-declines.py` / `fact-frontier.py`, anything
under `crates/`, `python/axeyum/agent/`.

## Verification run

```
python3 scripts/validate-autogenesis-operations.py
  AUTOGENESIS_OPERATIONS_OK|operations=28|registry=d98041d3...
python3 -m unittest scripts.tests.test_validate_autogenesis_operations
  Ran 34 tests in 0.277s -- OK
python3 scripts/tests/mutation_controls.py autogenesis-authored-declaration-driver
  exit 0, all 8 guards killed exactly their own test
python3 scripts/validate-facts.py
  806 facts checked, 0 errors
python3 scripts/check-autogenesis-holdout-isolation.py
  AUTOGENESIS_HOLDOUT_ISOLATION|held_out=37|files_scanned=1100|settled=0|references=0|verdict=PASS
python3 scripts/gen-production-provenance-ledger.py
  PRODUCTION_PROVENANCE|settled=628|via_multi_target=14|via_capsule=21|no_operation=593|multi_target_operations=4|multi_target_fixture=0|operations=28
```
