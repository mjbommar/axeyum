# ADR-3400: Statute time template carries calendar and applicability inputs

Status: accepted (bounded contract; final integration gates remain open)
Date: 2026-10-11

The first statute template models positive day periods under the 2025 edition
of Minnesota §645.15. §§645.13 (successive-week publication) and 645.14 (month
periods) are explicit exclusions. The caller must supply applicability and both
exclusion facts, plus a sourced holiday classification complete within an
inclusive date window. Missing facts are never treated as false. §645.44 subd.5
contains branch-specific holiday distinctions; this template does not guess them.

Nominal endpoint is start plus a positive day count; weekend/holiday endpoints
roll forward to the first admitted date. This is a stated modeling interpretation
of omitting a last day, not an independent legal applicability finding. Dates
outside calendar coverage or Gregorian range and exhausted rollover budgets
decline with no returned deadline. Periods cap at 36600 days; rollover caps at
366 days (default 32). Output records nominal date, skipped endpoints and source.

Source edition/text identity/retrieval date are pinned separately. Retrieval is
not an effective date. Initial outcomes are computed, not proof-certified;
independent reference and native constraints now validate bounded cases.
Verification reconstructs three obligations without calling the producer and
records verdict, check status, reason, serialized source and evidence separately.
checked-native requires verified evidence and certified reductions for every
obligation; otherwise decided agreement is only validated. Wrong decided verdicts
reject; unknown/missing coverage stays inconclusive. Checked UNSAT routes remain
required before proof credit.
The new statute-template manifest is outside the seven example-pack validator
until its unknown effective-interval evidence can be represented explicitly.
No fabricated from date is introduced merely to satisfy the current schema.

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
