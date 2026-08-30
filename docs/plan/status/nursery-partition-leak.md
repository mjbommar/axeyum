# Lane: nursery-partition-leak — the nursery split gate names what it finds

<!-- plan-section: lane-status -->

**In progress** (`WIP`, nursery-partition-leak, 2026-08-30). Reproduced
`check-autogenesis-nursery.py` red on a clean checkout: the sole stderr line is
`autogenesis-nursery: declared dependency component crosses evaluation
partitions`, naming no component, no fact, no partition.

Diagnosed against `artifacts/autogenesis/nursery-v1.json` directly (not
inherited from any prior lane's report): **3 declared-dependency components
cross evaluation partitions**, all train/development, **zero held-out
involvement**. A 4th, overlapping check (`evaluation population shares a
component with Autogenesis-1`) is masked behind the first raise and would also
fire once the first is silenced — it names 8 evaluation facts (7 train, 1
development) sharing a component with the two longitudinal Autogenesis-1
facts via `F:nat-mul-one`/`F:nat-zero-add`.

Root cause identified via `git log`: nursery-v1 froze 2026-08-18 against the
fact ledger's `depends_on` graph AS IT STOOD THEN. Commit `237c1abdd`
(2026-08-29, unrelated ledger-hygiene fix) retroactively added 1,054 missing
`depends_on` edges across 306 facts, reflecting REAL kernel proof-term
dependencies that existed but were never recorded. Several of those newly
surfaced edges cross nursery-v1's frozen partition boundaries. Nobody re-ran
this gate after that commit landed.

All 18 facts across the 3 crossing components are independently verified
`epistemic_status: proved`, and zero autogenesis operations
(`artifacts/autogenesis/operations.json`) reference any of them — proved by
ordinary hand development, unrelated to autogenesis dispatch.

Next: land the detailed-message fix, a scoped/checked exemption for these
specific components (amendment ledger discipline — no deletion, no silent
partition move), guard tests with a mutation kill table, and an ADR
(0850) recording the exemption and flagging the open policy question (should
train/development get a "spent-by-ordinary-development" amendment path
analogous to ADR-0542's held-out one?) for a decision above this lane's level.

<!-- plan-section: landed-changes -->

| 2026-08-30 | (pending) | Diagnosis and initial status doc. |
