# Lane: persona-absence-audit — check every absence claim in the twelve persona reviews

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, persona-absence-audit, 2026-09-04).** Auditing every
claim of absence in `docs/math-department/`'s twelve persona files against the
kernel, not against the ledger's prose. Two such claims are already known false
in the same direction (probability "one theorem"; the FTC listed as missing a
week after both directions were admitted). Deliverables: `AUDIT-2026-09-04.md`
with one row per checked claim, and ADR-1605 on the root cause — the ledger
cannot distinguish "no prose has been written" from "there is nothing here",
because 1,054 of 2,764 facts carry `gen-kernel-facts.py`'s deliberately
uncharacterising prose.

<!-- plan-section: landed-changes -->

| 2026-09-04 | persona-absence-audit | lane opened; auditing the twelve persona files' absence claims |
