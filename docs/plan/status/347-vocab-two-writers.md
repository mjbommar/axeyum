# 347 — vocab two writers

<!-- plan-section: lane-status -->

**IN PROGRESS.** `artifacts/autogenesis/mathlib-statable-vocabulary-v1.json`
has two writers; `gen-autogenesis-nursery-refill.py --check` has been RED on
`main` since 04:23 and its advice would delete `bridge_provenance` and
`row_digest`.

Measured so far: the two producers agree **exactly** on the substantive
derived content — `bridge` (72 entries) and `settled` (174 rows) are equal
element for element. The refill generator's document is a strict SUBSET: it
omits `bridge_provenance`, `row_digest`, the four `bridge_*` coverage counts,
and carries a shorter `derivation`. So the staleness `--check` reports is
real and is caused entirely by the second writer being poorer, not by any
disagreement about the mathematics.

Fix in progress. This commit is an early checkpoint and carries no code.
