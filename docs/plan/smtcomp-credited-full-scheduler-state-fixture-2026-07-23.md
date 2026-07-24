# SMT-COMP credited full scheduler-state fixture

Status: process-free E3 lifecycle derivation integrated on the SMT topic; no
live F2 acceptance, F3 cell, or F4 result

Date: 2026-07-23

Plan: [credited full-population execution plan](smtcomp-credited-full-population-plan-2026-07-23.md)

Predecessor: [full-cell admission fixture](smtcomp-credited-full-admission-fixture-2026-07-23.md)

## Result

The admitted-wave entry point no longer accepts caller-supplied open-attempt,
failed-allocation, or lost-allocation lists. It derives one deterministic,
self-sealed scheduler-state record from the canonical E3 allocation attempt
and terminal store after replaying command ownership, record seals, terminal
outcomes, and byte-exact stdout/stderr sidecars.

Each attempt row binds allocation and attempt IDs, the attempt-record digest,
terminal status, and terminal-record digest. The validator recomputes the exact
sorted open, failed, and lost projections. Omitting an open attempt, relabeling
a terminal, duplicating an allocation, reordering a row, or pairing a terminal
with another launch rejects or changes the state identity.

Scheduler-decision schema v2 binds the state-record digest. More importantly,
the scheduler accepts the complete record rather than an independent digest
and three lists: it validates the record against the exact plan/run/cell and
schedule allocation inventory, then reads only its recomputed projections.
This closes the remaining mismatch route in the low-level fixture API as well
as the admitted production entry point.

The lifecycle record is taken before a wave starts. A successful wave still
publishes an immutable checkpoint that binds the resulting allocation
terminals. Restart derives a fresh lifecycle record before deciding whether
the next wave may launch.

## Gates

The affected population, admitted-execution, and E3 suites pass 46 tests. They
cover empty state, completed state, a missing terminal becoming an exact open
attempt, failed-terminal projection, fully resealed projection omission, state
identity sensitivity, admitted launch blocking, and successful checkpoint
progression.

The complete `./scripts/check-smtcomp-resume.sh` gate passes 140 tests with one
expected live-host skip.

## Claim boundary

This is process-free fixture evidence. It did not probe a host, read or mutate
a live NAS run, create a resource session, launch or stop a systemd unit, or
run a solver. It creates no F2 acceptance manifest or F3/F4 result. Integration
and both repository readiness gates remain mandatory before any live
preparation or admission.
