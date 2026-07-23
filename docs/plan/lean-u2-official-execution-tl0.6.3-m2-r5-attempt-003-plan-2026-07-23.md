# Lean U2 TL0.6.3 M2 R5 attempt-003 plan

Status: **preregistered; no R5 implementation, control, harness, discovery, or
selected process exists**

Date: 2026-07-23

Parents:
[R4 plan](lean-u2-official-execution-tl0.6.3-m2-r4-attempt-003-plan-2026-07-23.md)
and [R4 control result](lean-u2-official-execution-tl0.6.3-m2-r4-control-result-2026-07-23.md).

## 1. Decision boundary

R5 authorizes implementation and offline qualification of a new 32 GiB local
address-space lane. It first requires one completion-grade, no-credit released-
Lean fanout control. Only a valid control may authorize at most one selected
process for the unchanged 64-case shard. R5 preserves the 512 MiB universal
stack, one CTest worker, one-hour selected watchdog, exact command/order,
family-specific artifact model, and completion-last tiered store.

No R5 implementation, control, harness, discovery, or selected process may run
until this plan is committed and pushed. Implementation/offline tests and their
documentation checkpoint must then be committed and pushed separately. The
control and selected process, if authorized, must use that same clean remote-
equal revision.

## 2. Frozen consumed and unconsumed history

R1 remains invalid, R2 remains its zero-process diagnostic closure, and R3
remains consumed by terminal `c228a80e...6c6f6` with zero credit. R4's corrected
control ran from `628c5911` under 17,179,869,184-byte `RLIMIT_AS`; stack
propagation passed, then the 274-byte nine-task source emitted the exact
24-byte `failed to create thread\n`, reached a diagnostic
16,504,496,128-byte `VmPeak`, timed out, and left no live process.

R4 never created its selected work/evidence root, harness, discovery, prelaunch
record, or selected process. Therefore selected `attempt-003` / sequence 3 is
still unconsumed. R5 validates that absence and reuses the selected attempt
identity without counting any control as an attempt or outcome.

## 3. Source-backed resource decision

Pinned Lean runtime `src/runtime/thread.cpp` (SHA-256
`f486a3051c5b3c8a9b569b4b76a7624e72a6a30d8589d17200194188eb2b055c`)
sets every Lean thread through `pthread_attr_setstacksize`, and
`LEAN_STACK_SIZE_KB=524288` becomes 536,870,912 bytes plus the runtime buffer.
Pinned `Init.Core` defines priority 9 as `Task.Priority.dedicated`, which starts
a dedicated worker rather than using the regular pool. The exact official
`channel.lean` source (SHA-256
`984bedcc89cba1292394ce2bc7578461e3415ba89236566bb05fbec4556f4f71`)
constructs up to eight simultaneous dedicated tasks in its four-producer/four-
consumer path. See the pinned official
[`thread.cpp`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/runtime/thread.cpp),
[`Init.Core`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Init/Core.lean),
and [`channel.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/compile_bench/channel.lean).

R4's limit failed with only 675,373,056 bytes between observed peak and limit.
R5 doubles that ceiling once, to 34,359,738,368 bytes. It does not reduce the
already qualified recursion margin, weaken the nine-task control, add a per-
test timeout, change official registration, or infer provider capacity.

## 4. Attempt and lane identity

| Field | Frozen value |
|---|---|
| run ID | `tl0.6.3-m2-release-linux-shard-0001-v4` |
| selected attempt / sequence | `attempt-003` / 3 |
| shard | unchanged membership shard `0001`, offsets `[64,128)`, exact 64 cases |
| implementation | full clean pushed R5 invocation revision |
| control root | new `/home/mjbommar/.cache/axeyum-tl063-m2-r5-control-<short-revision>` |
| private work root | new `/home/mjbommar/.cache/axeyum-tl063-m2-r5-<short-revision>` |
| evidence root | `docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m2-shard-0001-r5-attempt-003/` |
| selected process count | zero before invocation; exactly one if authorized |
| CTest | exact harness, `-j1`, one-hour watchdog |
| memory | 32 GiB `RLIMIT_AS` = 34,359,738,368 bytes per control/selected process |
| stack | universal `LEAN_STACK_SIZE_KB=524288` |

Any preflight mismatch stops before control or harness construction. A control
failure blocks R5 but does not consume selected attempt 003. Once selected
discovery or CTest exists, attempt 003 is consumed and cannot retry.

## 5. Completion-grade fanout control

R5 reuses exactly the corrected 274-byte source with SHA-256
`1896ef8218e617aff7557e1c1bcd14790207029e0c7ce3850d9403f2d1df1db3`.
It creates nine dedicated tasks, joins all nine through `IO.wait`/`IO.ofExcept`,
performs no channel or selected-case work, and must print exactly:

```text
R4_FANOUT_OK|tasks=9|sum=36
```

The label remains R4 because changing proven source bytes would confound the
resource-only comparison. The control root must be installed completion last
and retain source, canonical spec/prelaunch/terminal/completion records, raw
stdout/stderr, exact command/environment, wall time, peak direct-child RSS,
periodic direct-process `VmPeak`/`VmSize`/`VmRSS`/thread samples when available,
32 GiB limit, reaped-child state, and zero live group members. Both success and
failure are valid retained terminal evidence, but only clean exit 0, exact
stdout, empty stderr, complete join, and empty cleanup authorize selected
execution. Every control selection and credit field is empty/zero.

The existing direct environment probe also remains required. Host preflight
records `MemAvailable`, `CommitLimit`, `Committed_AS`, swap, overcommit mode,
PID limit, and source/toolchain identity; these values are diagnostic and do
not become performance or provider evidence.

## 6. Selected evidence and credit closure

R5 freshly derives the exact 124 generated rows and preserves R3/R4's
64 outcome captures plus three logs retained by bytes, 56 C/executable rows
metadata-only, and one wrapper retained as a harness artifact. Original-source
mutation, linked/extra/missing paths, invalid terminal/JUnit/store, partial
completion, or overwrite invalidates selected credit.

Only a clean exited CTest with exact 64-row no-skip JUnit and complete store may
credit exactly 64 local official outcomes. Parent/provider/Axeyum/pair/
performance/complete-population/axis/gate/parity counters remain zero. Any
selected timeout, signal, limit, JUnit, artifact, or store failure is retained
with zero outcomes and consumes attempt 003.

## 7. Gates and stop

Tests cover exact R1-R4 history, R4 selected-root absence, reused attempt
identity, new run/root non-reuse, one-variable 16-to-32 GiB resource delta,
unchanged wrapper/source/shard/order, success and thread-failure control
terminals, timeout cleanup, completion-last conflicts, source/raw/sample
tampering, empty control credit, 32 GiB process classification, 124/67/56/1
selected closure, JUnit/store mutations, CLI smoke, and absence of implicit
control or selected execution. Full parity generation, the known unrelated
link exception, and clean local/tracking/remote equality must pass.

R5 stops on any mismatch and never changes memory, stack, timeout, shard,
command, control source, or storage policy after observation. Even a valid
64-case completion closes only one local physical shard, not Lean 4 parity.
