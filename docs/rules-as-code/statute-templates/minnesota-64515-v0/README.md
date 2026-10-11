# Minnesota day-period template

A bounded source-linked template with computed results and a replayable finite
candidate certificate. Native SMT UNSAT evidence remains separately uncertified.
See [source](source.md), [crosswalk](model.md), [manifest](manifest.json) and
[example](example.py). Copy these files as a starting format for future statutes:
source edition/identity, unresolved applicability/effective intervals, a clause
crosswalk, explicit domain exclusions and calendar authority, executable example,
independent reference, then native obligations and checked proof routes.

This directory is separate from the seven illustrative packs. Its manifest
records an unknown effective interval instead of inventing a date required by
the older example-pack metadata schema. Validator/dashboard integration and
native proof obligations remain open work.

[Certificate fixture](fixtures/weekend-holiday.certificate.json) binds a synthetic
calendar, its complete candidate window and the claimed least endpoint. Replay
with `axeyum.rules.check_deadline_certificate`; use `expected_subject` to bind an
external query. `checked` establishes the bounded conditional endpoint, not
calendar authenticity, legal applicability, kernel admission or a general SMT
refutation. ADR-3500 records the format and checking boundary.
