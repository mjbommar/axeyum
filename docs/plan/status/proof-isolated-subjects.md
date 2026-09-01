# Lane: proof-isolated-subjects — how a proof-isolated import states its subject

<!-- plan-section: lane-status -->

**In progress (`proof-isolated-subjects`, 2026-08-31).** Investigating the
~36-40 `ml430-*` facts that `scripts/check-trust-closure.py` cannot resolve a
subject for because their declaration is admitted into an ephemeral,
proof-isolated `Kernel` instance and never merged into the persistent
environment `kernel_declaration_projection` walks.

Live measurement (against a captured projection): `kernel_facts=2183`,
`resolved=2112`, `unresolved=62`.

<!-- plan-section: landed-changes -->

| 2026-08-31 | | (in progress) |
