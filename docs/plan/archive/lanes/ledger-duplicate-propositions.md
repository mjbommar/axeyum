# Lane: ledger-duplicate-propositions — repair S2's 15 duplicate-proposition identity classes

<!-- plan-section: lane-status -->

**DONE (`ledger-duplicate-propositions`, 2026-08-30).** ADR-0771 (S2 trust-closure)
measured 15 identity classes (theorem pairs sharing a byte-identical
`Kernel::render_lean` canonical type), all 15 with both members registered as
ledger facts -- 15 propositions counted as 2,121 proved facts twice. This lane
verified all 15 by hand against `formal.statement` and each proof closure;
**all 15 survived scrutiny as genuine duplicates**, none rejected as "proved
from but strictly stronger." See ADR-0790 for the full breakdown, including
the two pairs (`CPoint.apollonius_from_stewart`/`_median`,
`Int.add_mul`/`Rat.int_right_distrib`) proved **independently** rather than
via one reusing the other's closure.

Facts are never deleted (ADR-0542, restated for facts here as ADR-0790): one
member of each pair now carries a new `equivalent_to: ["F:..."]` field
(`artifacts/ontology/fact.schema.json`), pointing at a canonical survivor.
Both members stay `proved`. `scripts/check-proposition-duplication.py` gates
any NEW unlabeled duplicate pair from entering, and
`scripts/validate-facts.py`'s summary now prints DISTINCT PROPOSITIONS
ESTABLISHED beside FACTS SETTLED so the two numbers cannot be quoted apart
again.

Corrected numbers: **2,123 facts settled** (`proved` 2,121 + `computed` 2),
**15 restate a sibling**, **2,108 distinct propositions established**
overall -- or, matching the original headline's own scope, **2,106 distinct
propositions** among the 2,121 `proved` facts alone.

Nothing else in this repository changed status: no fact's `epistemic_status`
flipped, no held-out nursery row was touched, `scripts/check-trust-closure.py`
(S2's own file) was not edited.

<!-- plan-section: landed-changes -->

| 2026-08-30 | 6174be234 | Add `equivalent_to` to `fact.schema.json` and mark all 15 non-canonical duplicate facts with it (surgical text-append edits, `statement`/`formal.statement` untouched); land `scripts/check-proposition-duplication.py` v1 (still failing at 15 unlabeled pairs at this commit, by design -- see report). |
| 2026-08-30 | (this session, later commits) | ADR-0790; `scripts/validate-facts.py` prints the FACTS SETTLED / DISTINCT PROPOSITIONS ESTABLISHED split; `scripts/tests/test-proposition-duplication.sh` (9 cases, 8 guard mutations, each killing exactly one); gate registered in `justfile` and `scripts/check.sh` as `proposition-duplication` / `proposition-duplication-controls`. |
