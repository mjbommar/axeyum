# TL0.6.3 M0 R1 plan — explicit Lean-shell worker control

Status: **preregistered; no R1 harness or test process has run**

Date: 2026-07-22

Parent work:

- [`M0 plan`](lean-u2-official-execution-tl0.6.3-m0-plan-2026-07-22.md)
- [`attempt 001`](lean-u2-official-execution-tl0.6.3-m0-attempt-001-2026-07-22.md)
- [`TL0.6.3`](lean-system-implementation-plan-2026-07-21.md#tl06-u2-official-test-execution-slices)

## 1. Decision boundary

R1 is one retry of the same registered case, parent selection, official
source, released toolchain, command-level CTest preset/filter, 8 GiB
per-process address-space ceiling, and 120-second watchdog. It corrects two
attempt-001 adapter mistakes and nothing else:

1. `LEAN_NUM_THREADS=1` did not constrain the `lean` shell task manager; and
2. the release preset created three undeclared CTest operational logs; and
3. a duplicate ASCII-escaping JSON helper disagreed with the immutable
   store's accepted UTF-8 canonical serializer on two official test paths.

The only possible positive result remains one retained **local official-case
outcome** for `compile/534.lean`. R1 cannot complete the 3,678-case parent,
claim an official provider, create an Axeyum outcome or pair, publish a
performance comparison, advance A0--A11, satisfy G1--G10, or establish Lean
parity.

No R1 harness generation or test process may run until this plan and the
failed-attempt evidence/result are committed and pushed. The R1 implementation
must then be committed and pushed separately before the test process runs.

## 2. Frozen failed-attempt dependency

R1 must validate and retain the immutable attempt-001 namespace at
`docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m0-attempt-001-failed/`:

| Field | Frozen value |
|---|---|
| implementation revision | `bc59fda54a2b6d7aa253173e5203c0aa4c0461ca` |
| files | 18 |
| bytes | 4,757,134 |
| manifest domain | `axeyum-lean-u2-official-execution-attempt-evidence-v1` |
| manifest SHA-256 | `7b8452e0a003a11867d2fc2150c00af99a0a61f41b10238b88a3ed2bb3838065` |
| terminal record | `93d033a92b1ba13631cf754ec717cf6058afb5a76e4a617eab1891331d93a55e` |
| JUnit record | `03b4aec0d34fdbbadd9acae8327934d7d90da87593ae74ecd49cc01f0069f687` |
| closure | no `post.json`, `case.json`, or `completion.json` |
| credits | all zero |

The validator must reject a missing, added, writable, symlinked, noncanonical,
or byte/hash-drifted failed-attempt file. Attempt-001 records must validate
against their physical accepted-store UTF-8 bytes and their frozen legacy seal
digests; they must not be rewritten to a new seal. The three retained CTest
diagnostics are attempt evidence, not permission to reinterpret the JUnit
failure as a semantic case outcome.

## 3. Corrected worker contract

The lane becomes `official-ctest-local-8g-lean-j1-v2`. It keeps:

- exact 8,589,934,592-byte inherited per-process `RLIMIT_AS`;
- exact CTest `-j1`;
- unchanged Lean default 1 GiB task stack: no `-s/--tstack` option;
- 120,000 ms wall timeout and 1,000 ms termination grace;
- no aggregate cgroup, swap, process, or thread ceiling; and
- local-official-case-only credit.

The generated stage-1 wrapper must initialize these exact arrays before
sourcing the unmodified official runner:

```bash
TEST_LEAN_ARGS=(-j1)
TEST_LEANI_ARGS=(-j1)
```

The official `compile/run_test.sh` expands `TEST_LEAN_ARGS` in its `lean --c`
command and `TEST_LEANI_ARGS` in its `lean --run` command. The per-case
`source_init` remains authoritative and may change those arrays for a future
case; `compile/534.lean` has no `.init.sh`. R1 must discover and retain the
effective shell commands through CTest output/artifacts.

`LEAN_NUM_THREADS=1` remains in the process environment because the generated
executable enters the runtime `lean_init_task_manager` path. The evidence must
distinguish:

- CTest workers: one, explicit `-j1`;
- Lean compiler/interpreter shell workers: one, explicit test-array `-j1`;
- generated-program runtime workers: requested one through
  `LEAN_NUM_THREADS=1`; and
- OS thread ceiling: not enforced.

The attempt-001 claim that one Lean worker was already observed must not be
copied forward.

## 4. CTest preset artifacts

The child command remains:

```text
ctest --preset release --test-dir $HARNESS_BUILD -j1 \
  --output-junit $ATTEMPT_TMP/test-results.xml \
  -E foreign -R '^compile/534[.]lean$'
```

Discovery must still return exactly the singleton harness. R1 additionally
declares only these CTest-created source-tree paths:

```text
build/release/Testing/Temporary/CTestCostData.txt
build/release/Testing/Temporary/LastTest.log
build/release/Testing/Temporary/LastTestsFailed.log  # optional on pass
```

The first two must exist after an exited CTest attempt; the failed-list log is
allowed only when CTest reports a failure. Every present file must be retained
byte-for-byte under `artifacts/ctest/` and included in the post-run manifest.
Any other `build/`, source, sidecar, runner, utility, or generated path is a
new failure.

For a passing compile/interpret case, the original declared test outputs
remain exact and required:

```text
tests/with_stage1_test_env.sh
tests/compile/534.lean.c
tests/compile/534.lean.out
tests/compile/534.lean.out.produced
```

All 12,289 archived official source entries must remain byte/mode/symlink
identical. Generated paths are evidence, never upstream-source identity.

## 5. Attempt and evidence identities

R1 uses sequence `2`, attempt ID `attempt-002`, and a fresh private work root.
The successful evidence namespace, if any, is
`docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m0/`. It must bind:

1. the original M0 preregistration commit and this R1 preregistration commit;
2. the attempt-001 failed evidence manifest;
3. exact source, toolchain, local-tool, harness, discovery, run, resource,
   platform, command, environment, and prelaunch records;
4. raw stdout/stderr and terminal installed before JUnit validation;
5. raw/canonical JUnit, exact post-run artifacts, one case record, and
   completion installed last; and
6. a final authority that counts one local outcome at most while retaining
   both process attempts.

R1 must delete the duplicate canonical serializer and import/reuse the
immutable store contract's UTF-8 `canonical_bytes` implementation for
installation, loading, hashing, completion dependencies, and generated
authorities. Offline tests must include both frozen non-ASCII official source
paths and reject ASCII-escaped or otherwise alternate encodings. This
canonicalization correction changes only new R1 record identities; attempt 001
keeps its frozen legacy seals and physical bytes.

A passed JUnit requires exit zero, the complete four-file test output set,
the required two CTest logs, exact output-sidecar behavior, unchanged source,
and a clean process group. A genuine test failure may create one failed case
outcome only if the resource/worker/evidence contract itself is valid. Thread
creation, timeout, signal, malformed JUnit, source drift, undeclared artifact,
or store failure creates no case outcome.

## 6. Required offline gates

Before R1 execution, tests must additionally reject:

1. missing or drifted attempt-001 evidence and any retrospective outcome;
2. absent, duplicated, reordered, or changed `TEST_LEAN_ARGS=(-j1)` and
   `TEST_LEANI_ARGS=(-j1)` wrapper assignments;
3. any `-s/--tstack` option or changed 8 GiB envelope;
4. conflation of CTest, Lean-shell, runtime, and OS thread controls;
5. absent required CTest logs, a pass with `LastTestsFailed.log`, or any extra
   preset/build artifact;
6. ASCII-escaped/noncanonical UTF-8 records and either non-ASCII source path
   missing from the source manifest;
7. pass without all four generated case outputs;
8. sequence/attempt/work/evidence-root reuse; and
9. parent, provider, Axeyum, pair, performance, axis, gate, or parity credit.

Normal CI remains offline. It validates committed evidence and never fetches
Lean, constructs the harness, or reruns CTest.

## 7. Stop conditions

Stop and retain R1 as a second incomplete attempt if any frozen identity,
failed-evidence dependency, discovery, worker/resource observation, process
closure, JUnit relation, source/artifact closure, or immutable-store step
fails. Do not increase memory, lower the task stack, change the selected case,
remove the official preset, or retry again without a separately published R2
plan.

If R1 completes, TL0.6.3 remains partial at 1/3,678 local cases and all
complete-parity axes/gates remain unchanged.
