# TL0.7.4 R1 plan — explicit Lean task stack and failure closure

Status: **preregistered after attempt 001; no R1 control has run**

Date: 2026-07-22

Parent:

- [original source-first plan](lean-execution-acceptance-tl0.7.4-plan-2026-07-22.md)
- [attempt 001 result](lean-execution-acceptance-tl0.7.4-attempt-001-2026-07-22.md)

## 1. Revision boundary

Attempt 001 proved that the original 4 GiB compile control is not runnable
with Lean 4.30's default 1 GiB task-thread stack. It also exposed a retention
ordering bug: raw streams installed, but artifact validation raised before the
terminal record installed.

R1 changes only the compile-control stack input and failure closure:

1. rename the compile control to
   `pinned-lean-compile-preflight-4g-tstack512m`;
2. insert exact Lean option `-s524288` after `-j1`, selecting a 512 MiB task
   stack in the pinned CLI's documented KiB unit;
3. keep the exact 4 GiB `RLIMIT_AS`, one requested Lean worker, 60-second
   watchdog, source, Lean binary, environment, working-directory policy, and
   zero-credit selection; the OS-thread count is explicitly not enforced;
4. install raw streams and terminal evidence before checking for a successful
   output artifact; and
5. bind the failed-attempt evidence and its no-credit diagnostics into the
   final authority rather than deleting or silently replacing them.

The official export control remains byte-for-byte as preregistered. It may run
only after the R1 compile completion validates and must consume that completion's
owned `.olean`.

## 2. Revised exact compile command

```text
<exact-pinned-lean> -j1 -s524288 -o <private-run>/AxeyumProbe.olean <private-run>/AxeyumProbe.lean
```

`-s524288` means 524,288 KiB = 536,870,912 bytes. It was chosen before the R1
process from a no-credit matrix in which 64, 256, 512, and 768 MiB all exited
zero and produced the identical 9,672-byte `.olean`, while 960 MiB and 1 GiB
failed to create a thread under 4 GiB. The result must record the option in the
exact command and resource envelope as `task_stack_limit` with state
`observed`, value `536870912`, and unit `bytes`.

`-j1` and `LEAN_NUM_THREADS=1` record requested Lean work parallelism, not an
OS-thread ceiling. Attempt 001's trace observes multiple runtime threads even
with those settings. R1 therefore records `worker_limit` as one requested
worker but `thread_limit` as `not-enforced`/null. It must not claim that one OS
thread was observed or enforced.

R1 does not use `LEAN_STACK_SIZE_KB` as a substitute. The diagnostic showed
that changing that environment value alone did not prevent the later task
thread's default 1 GiB mapping. The pinned CLI option is the effective control
surface.

## 3. Failure evidence closure

The final result must retain two distinct evidence roots:

- `lean-execution-acceptance-tl0.7.4-attempt-001-failed/` for the original
  incomplete attempt and diagnostics; and
- `lean-execution-acceptance-tl0.7.4/` for the R1 compile and unchanged export
  controls.

The authority must rehash both. It must explicitly report three observed
external process attempts (one failed compile, one completed R1 compile, one
completed exporter), two completed controls, and zero U2/Axeyum/paired/
performance/parity credit. The original partial store is expected to lack
artifact, terminal, and completion records; this known runner defect is part
of the bounded result and cannot be upgraded into completion evidence.

For any future unsuccessful process, the R1 runner installs, in order:

1. manifest/spec/run/prelaunch before launch;
2. raw stdout/stderr after reaping;
3. the terminal record, regardless of exit class or artifact presence;
4. artifact records only when their bytes exist; and
5. completion only after every success predicate and exact dependency passes.

## 4. Source-first and stop conditions

This R1 plan and attempt-001 evidence must be committed and pushed before the
runner change. The corrected runner/tests must then be committed and pushed
before the R1 pair. Offline tests add mutations for the exact task-stack
option/metric and terminal-before-artifact failure ordering.

Stop without a second retry if:

- the R1 compile cannot exit zero under exact 4 GiB + `-s524288`;
- its `.olean` differs from the preregistered source attribution or cannot be
  installed immutably;
- an unsuccessful process again lacks a terminal record;
- the exporter differs by one byte from the committed reference; or
- any path needs U2, Axeyum, pairing, performance, or parity credit to pass.

Successful R1 still closes only TL0.7's local execution-policy prerequisite.
It does not establish that the 512 MiB task stack is appropriate for all U2
tests; TL0.6.3 must retain each official command/profile and treat stack limits
as explicit per-profile inputs.
