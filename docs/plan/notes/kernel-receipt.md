# Notes: kernel-receipt

Detail moved out of [`../status/kernel-receipt.md`](../status/kernel-receipt.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
