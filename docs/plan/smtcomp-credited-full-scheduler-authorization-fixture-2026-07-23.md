# SMT-COMP credited full scheduler authorization and recovery fixture

Status: process-free F3 authorization/recovery mechanism on the SMT topic; no
live F2 acceptance, F3 cell, or F4 result

Date: 2026-07-23

Plan: [credited full-population execution plan](smtcomp-credited-full-population-plan-2026-07-23.md)

Predecessor: [scheduler-state fixture](smtcomp-credited-full-scheduler-state-fixture-2026-07-23.md)

## Result

Every admitted scheduler decision is now installed as an immutable,
completion-last authorization before the launcher can run. The authorization
binds the exact admission, full derived allocation state, checkpoint prefix,
pre-wave thermal observations, flags, decision time, and complete scheduler
decision. Loading the contiguous event history replays each decision from
those inputs and rejects field, seal, prefix, ordering, or decision drift.

The allocation-state schema now projects completed allocations as well as
open, failed, and lost lifecycle state. Scheduler decision v4 checks the
projection against the checkpoint chain in both directions:

- a checkpoint cannot name an allocation without a validated completed
  terminal;
- a completed allocation missing from the checkpoint prefix cannot authorize
  another launch; and
- a historical failed/lost initial allocation stops blocking only after every
  shard it owned is closed in the checkpoint prefix by exact completed retry
  evidence.

When the process dies after all terminals are durable but before checkpoint
publication, the scheduler reconstructs the next exact wave checkpoint from
the sealed terminal projection. It emits a `recover-checkpoint` authorization
containing that complete checkpoint. The supervisor launches nothing, returns
`wave-checkpoint-recovered`, and the admitted wrapper installs the checkpoint
through the existing immutable completion-last publisher. Partial completion,
ambiguous initial/retry shard coverage, and future-wave completion remain
fail-closed.

## Interruption and mutation coverage

The fixture interrupts authorization after temporary-file `fsync`, proves the
target absent, quarantines the orphan, retries, and replays the installed
authorization exactly. A launcher spy proves an authorization persistence
failure prevents the first launch. Separate regressions prove that complete
uncheckpointed initial terminals and exact different-host retry terminals
recover without relaunch, while a partial completion remains blocked. The
admitted entry point persists both the authorization and recovered checkpoint
before returning.

The affected execution, population, and E3 suites pass 50 tests.

## Claim boundary

This is process-free fixture evidence. It did not probe a host, read or mutate
a live NAS run, create a resource session, launch or stop a systemd unit, or
run a solver. It creates no F2 acceptance manifest or F3/F4 result. A live
preparation still requires clean integrated `origin/main`, both registered
readiness gates, a separately reviewed host/sentinel capture, and a distinct
integrated acceptance before any cell admission.
