# ADR-3200: Python Date facade preserves source sorts over ordinal Int terms

Status: accepted (bounded contract; final integration gates remain open)
Date: 2026-10-11

Rules-as-Code needs calendar dates distinct from integers and durations. The
first Python facade uses existing integer IR and solver evidence rather than
adding a native Date head. Gregorian values match datetime.date years 1–9999;
datetime/timezone values are rejected. Date ± Duration yields Date; Date − Date
yields Duration. Comparison requires Date operands in the same context. Month
and year offsets are not defined. Duration constants are signed integral days;
Boolean values are rejected despite Python's int subclass relation.

Every Date term, including arithmetic results, adds ordinal range constraints.
An overflowing symbolic date makes those constraints unsatisfiable. Contexts
retain named Date/Duration source sorts and forbid duplicate names. Model lifting
converts only Date declarations, preserves missing values and rejects out-of-range
or ill-typed values rather than inventing dates. Raw terms remain available for
existing solver APIs. solve includes every accumulated range obligation; callers
using raw terms separately must explicitly include context constraints.

This facade admits no theorem. CheckResult, replay and proof statuses are those
of the native solver; SAT models must replay against the complete lowered
assertion list. Pack loading and a real-statute template remain separate work.
No complete CON-7 or native Rust Date-sort claim follows from this increment.

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
