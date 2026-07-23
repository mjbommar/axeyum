# Lean U2 TL0.6.3 M2 R3 attempt-002 plan

Status: **preregistered; no R3 implementation, harness, discovery, or process exists**

Date: 2026-07-23

Parents: [M2 plan](lean-u2-official-execution-tl0.6.3-m2-shard-0001-plan-2026-07-22.md),
[R1 invalid result](lean-u2-official-execution-tl0.6.3-m2-r1-result-2026-07-22.md),
and [R2 diagnostic result](lean-u2-official-execution-tl0.6.3-m2-r2-diagnostic-closure-result-2026-07-22.md).

## 1. Decision boundary

R3 authorizes one new process attempt for the unchanged 64-case shard. It fixes
two pre-observation contracts: universal Lean runtime stack control and the
family-specific/tiered artifact store measured by R2. It does not reinterpret
R1, reuse its root, skip a case, select a different shard, or claim provider,
Axeyum, pair, performance, population, axis, gate, or parity completion.

No implementation, harness, discovery, or selected process may run until this
plan is committed and pushed. The implementation and offline tests must then be
committed and pushed separately before attempt 002.

## 2. Frozen history

R1 remains invalid with zero outcome credit. Its authority physical/record
digests are
`df5f95b9ee4f96e576119e7225eac98f0329a1eadbfd901703287627af852dd6` /
`0df3ed527d28b12b17cd5a3c0db3970f01a98e7886452feefda3f02068edb9fe`.
R2 added zero processes and zero outcomes; its diagnostic post and completion
record identities are
`46494553ed39e06359b195be398205d330cb047623bf6f16fa028825ec69bd66` and
`5ef1040a692a7a72650868909f7477beddf770093e86e2162bec5ff3745d459b`.
All 152 retained files remain immutable. Attempt 002 must validate that history
without importing any of R1's 64 diagnostic rows as outcomes.

## 3. Attempt identity

| Field | Frozen value |
|---|---|
| run ID | `tl0.6.3-m2-release-linux-shard-0001-v2` |
| attempt / sequence | `attempt-002` / 2 |
| shard | unchanged membership shard `0001`, offsets `[64,128)` |
| implementation | full clean pushed R3 revision |
| private work root | new, revision-named `/home/mjbommar/.cache/axeyum-tl063-m2-r3-<revision>` |
| evidence root | `docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m2-shard-0001-r3-attempt-002/` |
| process count | exactly one |
| CTest | exact 64-case harness, `-j1`, one-hour watchdog, 8 GiB `RLIMIT_AS` |

Any preflight mismatch stops before harness construction. Once discovery or
the child process exists, R3 is consumed and cannot retry.

## 4. Universal stack correction

Pinned `src/runtime/thread.cpp` (SHA-256 `f486a305...055c`) defines a 1 GiB
64-bit default and reads `LEAN_STACK_SIZE_KB` in `lean_run_main` before creating
the main Lean thread. Pinned `src/Lean/Shell.lean` (SHA-256 `0de8cdba...d54`)
uses the same KiB rounding for `-s/--tstack`. Direct docparse invokes `lean`
without `TEST_LEAN_ARGS`; compiled channel programs also enter
`lean_run_main`. Therefore R3 exports:

```text
LEAN_STACK_SIZE_KB=524288
```

from the generated stage1 environment wrapper. This reaches direct Lean,
server descendants, and generated executables without editing official source.
The value is the previously accepted TL0.7.4 512 MiB control. Existing
`TEST_LEAN_ARGS=(-j1)`, `TEST_LEANI_ARGS=(-j1)`, and `LEAN_NUM_THREADS=1`
remain; the environment variable is stack control, not a claimed PID/thread
ceiling. No `LEAN_CC`, source edit, cgroup, swap, or provider claim is added.

Offline tests must prove the wrapper contains exactly one numeric export,
reject missing/duplicate/zero/non-numeric/changed values, and demonstrate with
a harmless released-toolchain probe that the environment reaches a direct
Lean runtime without running a selected case.

## 5. Family-specific and tiered evidence

R3 freezes R2's generated-path policy: compile/compile-bench retain
`.out.produced` plus `.c`/`.out` unless no-compile; docparse retains only
`.out.produced`; three CTest logs and the wrapper are global. Unexpected paths
reject.

The store retains bytes for all 64 `.out.produced` captures and three CTest
logs. Generated C and executable rows remain path/mode/byte/hash metadata in
post evidence but their bytes are not copied into Git. Completion records this
assurance split explicitly. It must never state that metadata-only
intermediates are byte-retained or independently replayable.

R2's observed 124/67/56/1 counts are a structural expectation, not permission
to reuse its hashes: R3 must derive fresh hashes and byte totals from attempt
002. Missing outcome captures, original-source mutation, extra paths,
symlinks, unsafe mappings, overwrite, or incomplete split rejects completion.

## 6. Result and credit rules

CTest exit 0 or 8 is eligible only with exact 64-row, no-skip JUnit, reaped
process group, immutable terminal/raw evidence, valid family-specific post,
and completion last. A valid completed observation may contain failures and
then credits exactly 64 local official outcomes split by JUnit. Because R1 was
invalid, these are at most 64 first credited unique cases.

All parent/provider/Axeyum/pair/performance/complete-population/axis/gate/parity
counters remain zero. A timeout, signal, missing row, stack/resource failure,
artifact/store failure, or any invalid evidence gives R3 zero outcomes and is
retained without retry.

## 7. Required offline gates

Tests must cover: exact R1/R2 history; attempt/root non-reuse; stack export and
direct-runtime probe; unchanged 64 registrations/discovery; family paths;
fresh retained/metadata split; no-overwrite completion-last store; mixed
pass/fail projection; invalid terminal/JUnit/artifact cases; zero terminal
promotion; direct CLI smoke; and absence of implicit execution. The full
Lean/parity suite, generators, link gate except registered unrelated failures,
and clean local/tracking/remote equality must pass before invocation.

## 8. Stop and non-claims

R3 stops on any difference and never adjusts stack size, memory, worker count,
shard, command, or storage policy after observation. Even 64 passing outcomes
would complete only this local physical shard, not Lean 4 parity.
