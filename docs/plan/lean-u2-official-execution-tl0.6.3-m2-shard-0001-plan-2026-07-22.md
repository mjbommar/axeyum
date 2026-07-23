# Lean U2 TL0.6.3 M2 shard-0001 execution plan

Status: **preregistered; no M2 harness, discovery, or test process has run**

Date: 2026-07-22

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Parent work:

- [M1 child-shard result](lean-u2-official-execution-tl0.6.3-m1-shard-result-2026-07-22.md);
- [M1 machine authority](lean-u2-official-child-shards-v1.json);
- [accepted M0/R3 result](lean-u2-official-execution-tl0.6.3-m0-r3-result-2026-07-22.md);
- [TL0.7 execution policy](lean-execution-acceptance-tl0.7.4-2026-07-22.md); and
- [complete-parity contract](lean4-complete-parity-contract-2026-07-22.md).

## 1. Decision boundary

M2 is the first execution preregistration over an M1-derived multi-case shard.
It will construct an isolated 64-registration CTest harness and, only after the
plan and implementation are separately committed and pushed, make at most one
initial process attempt.

The selected scheduling unit is:

```text
membership-6f5d4dadd9bc51b42521fd6bb07e6fd270f4b638a08156c28cfa6cf7a998a488--shard-0001
```

This shard is not a representative sample. It is the lowest ordinal in the
release Linux selection's shared membership with no historical M0 observation.
Shard `0000` remains pending; it was not redefined, removed, completed, or
credited. It contains `compile/534.lean`, so choosing `0001` avoids rerunning
the singleton and gives this attempt a maximum of 64 new unique case outcomes.
The rule is frozen now and may not be changed after observing discovery,
runtime, failure, or resource behavior.

M2 can establish only bounded **local official-case outcomes** and, if every
case has a valid terminal/JUnit record, completion of this derived physical
shard. It cannot complete a parent selection, any of the 111 declared official
attempts, an official workflow cell/provider, U2, a native Axeyum cell, a pair,
a performance comparison, an A-axis, a G-gate, or Lean parity.

No harness construction, CTest discovery, or test execution is authorized
until this plan is committed and pushed. Read-only inspection of committed
authorities and source used to preregister the plan is not an outcome.

## 2. Frozen authority inputs

The implementation must verify exact physical bytes and run each existing
semantic validator before producing a harness:

| Input | SHA-256 |
|---|---|
| `lean-u2-official-child-shards-v1.json` | `6a2ec0b3edd353f3deb76e805052d5d2465ed1c9dd59cf221b0d175d0ce5e3e9` |
| `lean-u2-test-authority-v1.json` | `d7446e7965bac100ac6b5c607cbb7c87b5b80063fc23b3ec998fff2736d5d18e` |
| `lean-u2-official-ci-profiles-v1.json` | `4817d177828797f9dab9e62cf7647732d2b9c3788db7b7b4e3461bc868948548` |
| `lean-u2-official-execution-tl0.6.3-m0-r3-v1.json` | `fe04cd96fb9f08c8a0e834ec11f954c3c8172912332da28fc2a92adf0cedb475` |
| `lean-execution-evidence-v1.json` | `83fbfeaf6baa4c1bd747ce80bba87a15aaf159bb164a7647cc8e3155282fa05a` |
| `lean-execution-process-v1.json` | `0fc2d552f8594e2285eef2f0307a9b4d5313024166f0256486b731366947c0bf` |
| `lean-execution-store-v1.json` | `e167c2054537d628bf1e0621bd6fb864bc8f38847aaf690b8767687ef1d1a647` |
| `lean-execution-acceptance-v1.json` | `bd3f01fc5ac61bbcfdf23a82055fd58d47cf8167240727ec35e51ceb2a4be05f` |

The implementation reuses only validated helpers, not old outcome
interpretations. Their current source identities are:

| Source | SHA-256 |
|---|---|
| `scripts/lean_u2_official_execution.py` | `47c779d5b465e32b1ffa8faf3598472ed2ac98bd058928494e65a68d4f205fc2` |
| `scripts/lean_u2_official_execution_r3.py` | `061a7eca2e54f274c7289de4217d80db9a02f8e6f611f31667f7f01f059d835d` |
| `scripts/lean_execution_process.py` | `96f6866f619563e9fc639ca360f40260d2c35b521b3fc67941675d22984b2007` |
| `scripts/lean_execution_store.py` | `06d388a49d927a2f1b65a4632cd6297b140a579cf80edd5177fc6849b62ec679` |

## 3. Exact parent and shard identities

The selected official provenance chain is unchanged from M0:

| Object | ID | Record SHA-256 |
|---|---|---|
| context | `release-tag-l3` | `a2757855ea11633699e982418e53ae86f7b8e6807764202bcc06a7eeb83463c2` |
| cell | `release-tag-l3--linux-release` | `4da2ce61fca4141c2b963bc3dc94610ceebd9fee9059d45607cd8a23a621519b` |
| declared attempt | `release-tag-l3--linux-release--primary` | `21e8b9540f42f4ea86c0eb52985b28b09cdd2c4ebb31cd34d723eaac028a48a3` |
| selection | `default-filtered-aec7358564e4` | `02132086eb928c862eb19e3523b376342b869d5a159b67f2afecdf3b80db46c2` |
| membership | `membership-6f5d4dadd9bc51b42521fd6bb07e6fd270f4b638a08156c28cfa6cf7a998a488` | selected-list digest `6f5d4dadd9bc51b42521fd6bb07e6fd270f4b638a08156c28cfa6cf7a998a488` |
| shard | membership ID plus `--shard-0001` | `642dae1bf4141647af80aa1f8be2af1903ca9e132e48fe838237395df3df82da` |

The shard is offsets `[64, 128)` of the exact 3,678-name parent. It contains 64
ordered cases, from `compile/uint_fold.lean` through
`docparse/block_0004.txt`, with child-list digest
`22fe1346f37d1ff0c5fce9730f526f62f13248558b5463c087fa3b8569531c7c`.
Its complete ordered IDs live only in the M1 authority; this plan does not
create a second hand-maintained list.

The frozen case shape is:

| Family | Kind | Output policy | Cases |
|---|---|---|---:|
| compile | pile | empty | 2 |
| compile | pile | exact | 3 |
| compile_bench | pile | empty | 4 |
| compile_bench | pile | exact | 20 |
| docparse | pile | exact | 35 |
| **total** | | | **64** |

Every case has zero historical observation in the M1 authority. The
implementation must resolve all case registrations and per-case seals through
the U2 authority and reject missing, extra, duplicate, reordered, renamed,
historically observed, or non-member IDs.

## 4. Isolated harness and discovery

The implementation will add a new M2 adapter and offline test module. It must
prepare source from `git archive` of the exact Lean commit into an isolated
temporary tree and verify the extracted source manifest. It may not use or
mutate a live Lean worktree.

The generated CTest harness contains exactly the 64 selected registrations in
their M1 order. For each case it materializes the normalized command, working
directory, and properties from the U2 authority, substituting only the
declared `$BASH`, `$LEAN_ROOT`, `$HARNESS_ROOT`, `$BUILD_ROOT`, and `$PYTHON3`
path tokens. It may not edit official sources, runners, sidecars, expected
outputs, arguments, or success rules.

Prelaunch discovery is mandatory:

```text
ctest --test-dir $HARNESS_BUILD --show-only=json-v1 -E foreign
```

The normalized discovery must contain exactly 64 tests in the frozen order,
with exact names, commands, working directories, and properties. A mismatch is
`preflight-invalid`; no test process follows and no case outcome is recorded.

The single authorized child process command is:

```text
ctest --preset release --test-dir $HARNESS_BUILD -j1 \
  --output-junit $ATTEMPT_TMP/test-results.xml -E foreign
```

The harness itself is the declared shard restriction; M2 adds no generated
regular expression and no per-test timeout. The parent attempt remains
`not-run` because the other 3,614 selected names are absent from the child
harness.

## 5. Executable, environment, and resource lane

M2 revalidates the full released Lean toolchain manifest used by M0/R3. The
front executable pins remain:

| Executable | SHA-256 | Version boundary |
|---|---|---|
| `lean` | `3e0d0d3d801675359f2d4cf9815bfdb417b20b92fdd9d48b3b14c95bbae28bbf` | Lean 4.30.0 release at the target commit |
| `leanc` | `519d91f0c9e94c453d420de1ba9d3221c801e3332d4cfc399fc90931c41c23b2` | bundled clang 19.1.2 |
| `lake` | `d3e1f322c08d87f0d5850132a0b0309c1edbe53d641276b344717da448c8bc8b` | Lake 5.0.0-src+d024af0 |

The M2 lane ID is
`official-ctest-local-8g-lean-j1-shard64-v1`:

| Field | Frozen value |
|---|---|
| memory | 8,589,934,592-byte per-process `RLIMIT_AS`, inherited by descendants |
| CTest workers | exactly 1 (`-j1`) |
| Lean workers | `TEST_LEAN_ARGS=(-j1)` and `TEST_LEANI_ARGS=(-j1)` |
| `LEAN_NUM_THREADS` | `1`, retained as environment evidence but not treated as sufficient worker enforcement |
| compiler override | absent; `LEAN_CC` must be unset |
| task-stack override | none |
| wall watchdog | 3,600,000 ms |
| termination grace | 1,000 ms, then process-group `SIGKILL` |
| per-test timeout | none added |
| aggregate cgroup/PID/swap/disk ceiling | not enforced / null |
| network | not required by the declared commands; no network identity or provider claim |

The hour wall is a shard-process budget, not a performance target and not an
official workflow limit. The process record must retain exact argv,
environment, working directory, UTC interval, executable/toolchain/source/
harness identities, `uname`, glibc, CPU count, filesystem type, termination,
and observed resource telemetry. A local host observation cannot fill the
declared `ubuntu-latest`/old-glibc provider cell.

## 6. Attempt and immutable evidence

The first and only process authorized by this preregistration is:

| Field | Value |
|---|---|
| run ID | `tl0.6.3-m2-release-linux-shard-0001-v1` |
| attempt ID | `attempt-001` |
| sequence | 1 |
| evidence root | `docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m2-shard-0001/` |

The runner must install immutable records in this order:

1. source, toolchain, platform, lane, run, shard, harness, discovery, and
   prelaunch identities;
2. raw CTest stdout and stderr;
3. terminal evidence before interpreting JUnit or artifacts;
4. raw JUnit and canonical JUnit projection;
5. zero or 64 per-case records in exact shard order;
6. post-run source/harness and declared generated-artifact manifests; and
7. completion last over the exact dependency set.

Normal CTest exit 0 or 8 is eligible for result validation. To publish any M2
case outcome, JUnit must exist, parse, contain exactly the 64 selected names
once each, and classify every case as completed `passed` or `failed`; a skipped,
not-run, missing, duplicate, extra, or wrong-name row invalidates shard
completion. Exit/JUnit disagreement is invalid. A timeout, signal, launch,
preflight, malformed-JUnit, identity, source, harness, or evidence failure
publishes zero case outcomes rather than inferring partial completion from
stdout.

A valid 64-row result may contain official test failures and still complete the
observation shard: failures are official outcomes, not compatibility success.
The summary must report pass and failure counts separately. Shard completion
means all 64 official outcomes were retained; it does not mean they passed.

## 7. Credit and non-credit rules

For a valid complete result only:

- `official_cases = 64` and `official_outcomes = 64`;
- `unique_new_official_cases = 64` because the selected shard has no historical
  observations;
- `official_passes + official_failures = 64`;
- `local_physical_shards_completed = 1`; and
- all parent/profile/provider/native/pair/performance/terminal counters remain
  zero.

Any incomplete or invalid attempt has zero M2 case/shard credit. Attempt count
and diagnostic evidence remain visible but cannot be promoted into case
coverage. Duration and RSS are operational telemetry only; with no matched
Axeyum run they create no performance row.

The M1 scheduling authority remains immutable and `not-run`. M2 publishes a
separate result authority referencing it. Neither a pass total nor shard
completion may mutate the 111 parent attempt outcomes.

## 8. Required offline tests

Before any live attempt, focused tests must cover at least:

1. plan, authority, helper-source, target, toolchain, and shard-seal drift;
2. selection of anything other than the lowest-ordinal zero-history shard;
3. missing, extra, duplicate, reordered, renamed, non-member, or historical
   case IDs;
4. family/kind/output-policy aggregate drift;
5. command, path-token, working-directory, property, environment, compiler,
   worker, filter, or resource drift;
6. source/toolchain/harness file, symlink, mode, byte, or aggregate drift;
7. discovery count/order/name/command/property disagreement;
8. absent, malformed, duplicate, extra, wrong-name, skipped, or not-run JUnit
   rows;
9. exit/JUnit/case-outcome disagreement, including mixed pass/failure success;
10. source, sidecar, expected-output, runner, or undeclared-artifact mutation;
11. missing raw stream, terminal, case, dependency, or completion records;
12. completion-before-case, overwrite, orphan, order, hash, and byte drift; and
13. any parent/profile/provider/Axeyum/pair/performance/population/axis/gate/
    parity promotion.

Normal CI runs only offline validators against committed evidence. It must not
prepare Lean, generate a live harness, discover tests, or execute CTest.

## 9. Stop conditions and handoff

Stop before launch if any frozen input, tool, source archive, toolchain
manifest, harness, discovery row, process/store prerequisite, or lane field
differs. After launch, retain and classify the one attempt exactly; do not
silently repair, retry, widen the lane, skip a case, or change the shard. Any
retry requires a new source-first plan and sequence.

If attempt 001 produces a valid complete 64-row result, publish the immutable
authority and bounded result before selecting another shard. If it is
incomplete or invalid, publish the exact evidence and root cause before any
correction. TL0.6.4 native-surface classification may consume the exact case
list independently, but no native or paired result is implied by M2.
