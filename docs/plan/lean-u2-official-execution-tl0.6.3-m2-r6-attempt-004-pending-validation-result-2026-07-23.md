# Lean U2 TL0.6.3 M2 R6 attempt-004 pending-validation result

Status: **selected attempt consumed; complete-looking 64-pass store; zero credit
pending validator-only correction**

Date: 2026-07-23

Parents:
[R6 plan](lean-u2-official-execution-tl0.6.3-m2-r6-attempt-004-plan-2026-07-23.md)
and [control-history correction](lean-u2-official-execution-tl0.6.3-m2-r6-control-history-r1-implementation-2026-07-23.md).

## Observed execution

From clean remote-equal revision
`dc5880332a2805e050021bcf3f403574d3fae237`, the direct stack probe passed and
the fresh nine-task control authorized selected execution with completion
`60eef0458288eb02c43d379e4c8ae4df5054dd1bce8df035036e63af6f754a3e`.
Attempt 004 then ran exactly once.

The API command wrapper returned while the independently sessioned runner and
CTest were still live. Read-only PID monitoring showed the original runner and
CTest, not a retry. They completed without intervention and installed terminal,
JUnit, 64 cases, post, projection, and completion last.

Terminal `9d060439a088800cce1e900cfdf52d6be617956d9d0b33aa70c93f2879e60d81`
is clean exit 0 after 63,812 ms: no signal/watchdog, child reaped, empty live
group, and 34,359,738,368-byte `RLIMIT_AS`. JUnit
`77054383710c134239b7b002f154118d39958df62f3ac2c3357807aa27c25c50`
contains exact 64/64 passes and zero failures/skips. Post
`5297007237cbc08357f0210c872db40ef5adb4667d348b3cf431d3e470e2f5a1`
selects the all-pass branch: conditional failure log absent, 123 generated
rows, 66 retained payloads, 56 metadata-only rows, and one existing wrapper.

## Frozen store and fail-closed stop

Completion `1f0b9af8997d9cced7bbb141e979ecd169b882b3df57ae02b0cb5f34ff0f3b67`
was installed last and projects 64 local official outcomes / one local shard,
with all provider/Axeyum/pair/performance/population/axis/gate/parity fields
zero. The root contains 152 files / 5,246,140 bytes; portable domain
`r6-complete-evidence-pending-validation-v1` digest is
`73634b06b802b938c604aea100afd3aacf2f727f6ee8275f90566d69d1b3fdb3`.

Post-install validation then called the completion builder through its default
pre-install dependency mode. That mode correctly rejects an already-present
`completion.json`, so validation stopped with `R3 completion exists before
dependency validation`. No evidence byte was changed.

Attempt 004 is consumed and must not be rerun. Until a separately pushed
validator-only correction reconstructs the exact existing completion with
`allow_completion=true`, this document assigns zero R6 outcomes/shard credit.
The sealed projected fields are observations pending acceptance, not current
parity counters.
