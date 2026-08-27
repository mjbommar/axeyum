# Lane: kernel-receipt — a general kernel-lane execution driver for operation receipts

<!-- plan-section: lane-status -->

**Closed the "no shape for hand-authored kernel proof" gap doc 293 hit**
(`DONE`, kernel-receipt, 2026-08-27). Doc 293 proved five `Int.ModEq`
theorems directly against the kernel (no producer/import pipeline component
running at all) and could not register the retrospective receipt ADR-0602
calls for: `validate-autogenesis-operations.py`'s `EXECUTION_DRIVERS` was a
closed set of ten, eight of them `axeyum-lean-import/*` (pipelined) and two
named for one-off episodes. Per doc 288, 125 of 132 dependency-ready facts
are exactly this `proof-route-only` shape, so this was not a corner case.

Added `axeyum-lean-kernel/authored-declaration-v1` in
`scripts/validate-autogenesis-operations.py`: fields chosen to be
independently re-checkable (declaration name(s), the source file each must
literally appear in, and the exact test functions that must exist and fail
on their absence) rather than narrative. Registered doc 293's five closures
as ONE operation (`authoritative-kernel-int-modeq-shift-family-v1`) naming
all five facts, per the standing "`applicability.fact_ids` is a list, never
required length one" rule (doc 228). Full account:
[`docs/autogenesis/296-a-general-kernel-lane-execution-driver.md`](../../autogenesis/296-a-general-kernel-lane-execution-driver.md).

**Discrimination proven both ways.** Ten new tests in
`scripts/tests/test_validate_autogenesis_operations.py`: one positive (the
committed registration validates, and `gen-production-provenance-ledger.py`'s
`operation_widths()` reports it at width 5) and nine adversarial (absent
declaration, declaration bound twice, missing verifying test, source outside
the kernel crate, three malformed-name shapes, duplicate fact id, misordered
targets, applicability/fact-id mismatch, inconsistent admission tuple).
Eight mutation guards registered in `scripts/tests/mutation_controls.py`
(`autogenesis-authored-declaration-driver`); each kills exactly the one test
written for it (`python3 scripts/tests/mutation_controls.py
autogenesis-authored-declaration-driver`, exit 0). The first attempt at the
admission-consistency guard mutated the whole `elif` branch away and killed
five unrelated tests via collateral fallthrough into a different driver's
stricter Nat-only branch — fixed by mutating only the inner condition,
re-verified to kill exactly one.

**Measured, not assumed: the provenance ledger's generality counter is only
PARTIALLY moved by this registration.** `multi_target_operations` (derived
from `operations.json` alone) rose 3 -> 4 immediately. `facts_via_multi_target`
(the actual headline metric) did NOT credit doc 293's five facts — it joins
through `fact.evidence[].checker_operation.id`, which none of the five
facts' evidence rows carry, and editing `artifacts/facts/` was out of this
lane's scope. Left as a named next step for whichever lane next touches
those five facts' evidence.

**Amended ADR-0602** (append-only, per the repository's amendment
convention) recording that receipts could previously only describe
pipelined work and that this driver closes it.

**Also reported, not fixed** (another lane owns
`artifacts/autogenesis/producer-contracts/`): `int-modeq-family-v1`'s
`route: kernel-lane` label disagrees with its recipe (every operation ever
run against it is import-mediated); doc 293 found this, and this lane
re-confirms it now that a real `kernel-lane` driver exists to compare
against. Recommendation: re-label the contract's `route` to `import`, or
add a sibling `kernel-lane` contract naming `authored-declaration-v1`.

Verification: `python3 scripts/validate-autogenesis-operations.py` —
`AUTOGENESIS_OPERATIONS_OK|operations=28`. `python3 -m unittest
scripts.tests.test_validate_autogenesis_operations` — 34 passed. `python3
scripts/tests/mutation_controls.py autogenesis-authored-declaration-driver`
— exit 0, all 8 guards kill exactly their own test. `python3
scripts/validate-facts.py` — 806 facts, 0 errors (unchanged by this lane;
`artifacts/facts/` was not touched). `python3
scripts/check-autogenesis-holdout-isolation.py` — PASS, held_out=37.
`python3 scripts/gen-production-provenance-ledger.py` (regenerated, since
`operations.json` is its sole non-fact input and the aggregate gate checks
it stays fresh) —
`multi_target_operations=4` (was 3). `python3 scripts/gen-adr-index.py
--check` — unchanged (ADR-0602's front matter was not touched, only its
body).

<!-- plan-section: landed-changes -->

| 2026-08-27 | (pending) | New `axeyum-lean-kernel/authored-declaration-v1` execution driver in `scripts/validate-autogenesis-operations.py` (re-checkable fields: declaration source/test file existence, literal declaration-in-source check, literal test-function-in-file check, fact-id binding order); registered doc 293's five `Int.ModEq` closures as one operation; ten discrimination tests + eight mutation-verified guards; ADR-0602 amendment; `docs/autogenesis/296`; regenerated `docs/plan/generated/production-provenance-ledger.md`. |
