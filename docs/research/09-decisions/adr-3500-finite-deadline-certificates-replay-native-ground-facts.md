# ADR-3500: Finite deadline certificates replay native ground facts

Status: accepted (bounded contract; final integration gates remain open)
Date: 2026-10-11

Deadline verification needs checkable evidence beyond bare UNSAT. Version 1
JSON carries the complete conditional subject (date/day count, applicability
flags, calendar coverage/source/all holiday facts, rollover bound), claimed
endpoint and every candidate's date/weekday/holiday observations in order.
Deterministic serialization sorts keys and holidays. Limit: 256 KiB, 4096 holidays,
367 candidates. Duplicate fields, noncanonical dates and unknown envelope fields
reject; future versions are unsupported; byte exhaustion is resource-limited.

The checker does not call the deadline producer. It reconstructs the authoritative
candidate span, computes weekday through native ground ordinal modulo arithmetic,
checks each calendar observation, rejects any admitted predecessor and requires
the claimed candidate to be admitted. This proves the unique least endpoint of
this bounded population under its declared assumptions. Optional expected_subject
binds the artifact to an external query with JSON type distinctions preserved.
A self-contained replay proves only the subject carried in the artifact.

Producer arithmetic uses datetime.weekday; replay uses the existing trusted IR
ground evaluator. Calendar validation/encoding code is shared, so implementation
independence is not claimed. No source authenticity, holiday completeness, legal
applicability, kernel admission or general SMT proof follows. Native UNSAT evidence
remains separately reported as uncertified. Changed claim, candidate population,
arithmetic/calendar witness or expected source context must fail. A private guard
mutation must kill exactly one targeted negative-control test.

## Adoption evidence — 2026-10-11

The implementation and negative controls were reviewed against this contract.
The fresh native consumer population includes the Date, pack metadata, pack
evaluation and deadline tests: 1166 passed, with one unrelated external SAT
checker test skipped. That external route passed separately with its configured
guarded checker. The offline validator controls were rerun at adoption: 20
tests passed; the recorded template validation checks four source snapshots
and replays one conditional certificate. Detailed provenance and private guard
controls remain in the [feedback completion audit](../../plan/user-feedback-completion-audit-2026-10-11.md)
and [lane receipts](../../plan/notes/28-wide-real-smtlib-writer.md).

Acceptance adopts the stated bounded design, not a claim of legal applicability,
native Rust Date support, general theorem admission or completion of the full
feedback goal. The implementation branch still awaits final workspace checks
and integration into main.
