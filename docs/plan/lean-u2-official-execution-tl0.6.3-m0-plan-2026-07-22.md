# TL0.6.3 M0 plan — first retained official U2 case shard

Status: **preregistered; no M0 harness or test process has run**

Date: 2026-07-22

Parent work:

- [`TL0.6.3`](lean-system-implementation-plan-2026-07-21.md#tl06-u2-official-test-execution-slices)
- [U2 registration authority](lean-u2-test-authority-v1.json)
- [official CI profile authority](lean-u2-official-ci-profiles-v1.json)
- [TL0.7.4 accepted execution path](lean-execution-acceptance-tl0.7.4-2026-07-22.md)
- [complete-parity contract](lean4-complete-parity-contract-2026-07-22.md)

## 1. Decision boundary

M0 is the first observation-producing TL0.6.3 slice. It executes exactly one
registered official Lean test case as a local shard of one exact official CI
selection. It exists to prove the case/JUnit/completion path before thousands
of cases are launched.

The only possible positive result is one retained **local official-case
outcome** for `compile/534.lean`. M0 cannot complete its 3,678-case parent
selection, complete an official GitHub Actions cell, claim the
`ubuntu-latest` or old-glibc provider environment, create an Axeyum outcome or
pair, publish a performance comparison, complete U2, advance A0--A11, satisfy
G1--G10, or establish Lean parity.

No harness generation, CTest discovery, or test process may run until this
plan is committed and pushed. Read-only source, Git, GitHub API, executable,
and host inspection used to write the plan is not an execution outcome.

## 2. Frozen upstream target

The target is official Lean release tag `v4.30.0`:

| Field | Frozen value |
|---|---|
| repository | `https://github.com/leanprover/lean4` |
| commit/tag target | `d024af099ca4bf2c86f649261ebf59565dc8c622` |
| commit tree | `0271450d1b109f9a0e5fadea2b6044160e9af7dd` |
| tag object type | direct `commit` |
| author timestamp | `2026-05-02T11:55:04Z` |
| committer timestamp | `2026-05-26T08:34:15Z` |

`git show`, `git ls-tree`, and `gh api` independently agreed on the commit and
direct tag before preregistration. The relevant official definitions are the
[test registration](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/CMakeLists.txt),
[test utilities](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/util.sh),
[build workflow](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/.github/workflows/build-template.yml),
and [CTest presets](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/CMakePresets.json).

Committed Axeyum inputs are frozen by current byte hash:

| Input | SHA-256 |
|---|---|
| `lean-u2-test-authority-v1.json` | `d7446e7965bac100ac6b5c607cbb7c87b5b80063fc23b3ec998fff2736d5d18e` |
| `lean-u2-official-ci-profiles-v1.json` | `4817d177828797f9dab9e62cf7647732d2b9c3788db7b7b4e3461bc868948548` |
| `lean-execution-evidence-v1.json` | `83fbfeaf6baa4c1bd747ce80bba87a15aaf159bb164a7647cc8e3155282fa05a` |
| `lean-execution-process-v1.json` | `0fc2d552f8594e2285eef2f0307a9b4d5313024166f0256486b731366947c0bf` |
| `lean-execution-store-v1.json` | `e167c2054537d628bf1e0621bd6fb864bc8f38847aaf690b8767687ef1d1a647` |
| `lean-execution-acceptance-v1.json` | `bd3f01fc5ac61bbcfdf23a82055fd58d47cf8167240727ec35e51ceb2a4be05f` |

## 3. Parent cell and exact one-case shard

M0 derives from exactly this profile chain:

| Object | ID | Record SHA-256 |
|---|---|---|
| context | `release-tag-l3` | `a2757855ea11633699e982418e53ae86f7b8e6807764202bcc06a7eeb83463c2` |
| cell | `release-tag-l3--linux-release` | `4da2ce61fca4141c2b963bc3dc94610ceebd9fee9059d45607cd8a23a621519b` |
| declared attempt | `release-tag-l3--linux-release--primary` | `21e8b9540f42f4ea86c0eb52985b28b09cdd2c4ebb31cd34d723eaac028a48a3` |
| selection | `default-filtered-aec7358564e4` | `02132086eb928c862eb19e3523b376342b869d5a159b67f2afecdf3b80db46c2` |
| case | `compile/534.lean` | `ea289dd25543d2e90f2da84b79b60598a3848b600262969a8babe228133c0d4f` |

The parent selection is the default 3,678-case registration filtered by
`-E foreign`. No registered name contains `foreign`, so it still selects all
3,678 ordered case IDs with digest
`6f5d4dadd9bc51b42521fd6bb07e6fd270f4b638a08156c28cfa6cf7a998a488`.
The M0 shard is the ordered singleton `['compile/534.lean']`; the validator
must prove membership in that exact parent list and reject extra, missing,
duplicate, reordered, renamed, or implicitly discovered cases.

The case is a `compile` pile test. Its registered command is:

```text
$BASH $LEAN_ROOT/tests/with_stage1_test_env.sh \
  $LEAN_ROOT/tests/compile/run_test.sh 534.lean
```

with working directory `$LEAN_ROOT/tests/compile`, process-exit-zero success,
and exact-output sidecar `tests/compile/534.lean.out.expected`. Frozen source
identities are:

| Source | Git blob | SHA-256 |
|---|---|---|
| `tests/compile/534.lean` | `549a977c012417f85436e54b6c3c18983096f429` | `720a6465ce5267560d754b2ebcfbbc237eb06c1a1aaf7d2e0dbd28522dad300e` |
| `tests/compile/534.lean.out.expected` | `45b983be36b73c0788dc9cbcb76cbb80fc7bb057` | `98ea6e4f216f2fb4b69fff9b3a44842c38686ca685f3f55dc48c5d3fb1107be4` |
| `tests/compile/run_test.sh` | `86722390dde323f946380ad1e955069ff33c3646` | `557fe4726ec23d812a0649c56def2c22daa89faeddc58b7e49b118f3ab123396` |
| `tests/util.sh` | `1652424bb7a452d58f6605d48160f9308833971a` | `55dbc20818948622b3a16072bed49d9ff5be31df4c766fdb8fa4cfb44c11c092` |
| `tests/with_env.sh.in` | `b6c12814e35a7898fa4bcce994594b5e3b24c427` | `57efe3131b6663ffa8ac3ed01eb18174c5ee4bd61a9331bda69b9dc8627aef97` |

M0 does not mutate the parent TL0.6.2 authority's declared attempt from
`not-run`. It publishes a separate child shard and retains the parent attempt
ID as provenance. Only a later execution of all 3,678 selected cases may
replace the parent attempt's not-run state.

## 4. Executable and local platform identity

The released Lean toolchain already used by TL0.7.4 is the M0 baseline:

| Executable | SHA-256 | Frozen version |
|---|---|---|
| `lean` | `3e0d0d3d801675359f2d4cf9815bfdb417b20b92fdd9d48b3b14c95bbae28bbf` | Lean 4.30.0, commit `d024af099c...`, Release |
| `leanc` | `519d91f0c9e94c453d420de1ba9d3221c801e3332d4cfc399fc90931c41c23b2` | clang 19.1.2, LLVM `7ba7d8e2...` |
| `lake` | `d3e1f322c08d87f0d5850132a0b0309c1edbe53d641276b344717da448c8bc8b` | Lake 5.0.0-src+d024af0 |

The runner must additionally retain a sorted, path-normalized manifest of all
regular files and symlinks reachable under the toolchain root. Pinning only
the front executable is insufficient because `lean`, `leanc`, imported
`.olean` files, headers, libraries, and compiler resources jointly determine
the observation.

Preregistered local tools are:

| Tool | Resolved implementation | SHA-256 | Version |
|---|---|---|---|
| Bash | `/usr/bin/bash` | `3efccc187bafa75ff1e37d246270ab3e7aa559f242c7a52bf3ec2a1b5450bdbd` | 5.3.9 |
| CMake | `/usr/bin/cmake` | `6e1dccda39845415d68eabb934c598998949c99ec4668625d571aee1827b05c7` | 4.2.3 |
| CTest | `/usr/bin/ctest` | `2cf8308ae2235efcae86a2eba443444f33ab611193a84092de33ec16836f5f17` | 4.2.3 |
| Python | `/usr/bin/python3.14` | `b8d8288faefdd300201f43fcf00f6f539a27218eeed3a3dff5ab10b9c4c99700` | 3.14.4 |
| C++ | `/usr/bin/x86_64-linux-gnu-g++-15` | `e6718f7e0c7d057c3ff77b550c603da9bc4030e3ede3c053705acce1293dbe4d` | GCC 15.2.0 |
| diff | `/usr/bin/diff` | `0abb2ec6b0a64efc7fa84747a8534f1d10a2d823599de932a8df4cabf31ca98e` | GNU diffutils 3.12 |
| Perl | `/usr/bin/perl` | `50036d900bc669506ea0899f0ad5c117806d6815c606cba442f955cd1b2ee1cf` | 5.40.1 |

Absolute live paths are evidence, not portable identity. Records must also
retain resolved path, full SHA-256, version output, argv, environment, working
directory, UTC time, `uname`, glibc, CPU count, filesystem type, and runner
revision.

The preregistration host observation is Linux x86_64, kernel
`7.0.0-27-generic`, glibc 2.43, 24 online CPUs, and an ext-family worktree.
These facts do not substitute for the run-time platform record and do not
claim the official workflow's `ubuntu-latest` or `oldGlibc` environment.

## 5. Source and harness construction

The implementation must prepare an isolated tree from `git archive` of the
exact commit, never from the dirty/no-checkout cache worktree. It must verify
the commit/tree first and hash the extracted regular-file/symlink manifest.
The authoritative source remains Git; generated harness files are separate
artifacts and may not overwrite a tracked source path.

The child CTest harness contains exactly one registration. It must substitute
the official registered tuple into absolute paths without changing the test
script or its argument:

- command: pinned Bash, generated stage-1 environment wrapper, official
  `tests/compile/run_test.sh`, `534.lean`;
- working directory: extracted `tests/compile`;
- stage: `1`;
- `SRC_DIR`, `TEST_DIR`, and `SCRIPT_DIR`: extracted official source paths;
- `BUILD_DIR`: pinned release-toolchain root;
- `PATH`: pinned toolchain `bin`, then `/usr/bin:/bin`;
- `LEAN_NUM_THREADS=1`, `LANG=C.UTF-8`, `LC_ALL=C.UTF-8`, `TZ=UTC`, and no
  network-dependent environment;
- `LEANC_OPTS`: the pinned toolchain include directory; and
- no source, expected-output, test-script, or utility edits.

Before launch, `ctest --show-only=json-v1` must return exactly one test whose
normalized name, command, working directory, and properties equal the frozen
case registration. Discovery mismatch is `preflight-invalid`, not a test
failure.

The parent command remains frozen as the TL0.6.2 record. M0's derived child
command is the one-worker, one-case restriction:

```text
ctest --preset release --test-dir $HARNESS_BUILD -j1 \
  --output-junit $ATTEMPT_TMP/test-results.xml \
  -E foreign -R '^compile/534[.]lean$'
```

The added `-R` creates the declared shard; it is why M0 cannot claim parent
attempt completion. The result must retain both normalized command shapes.

## 6. Registered resource lane

M0 introduces `official-ctest-local-8g-v1`; it does not alias either frozen
TL0.7 lane:

| Field | Value |
|---|---|
| purpose | local reproduction of an official registered CTest case |
| memory | 8,589,934,592-byte per-process `RLIMIT_AS`, inherited by descendants |
| CTest workers | exactly 1 (`-j1`) |
| Lean workers | requested 1 through `LEAN_NUM_THREADS=1` |
| OS thread ceiling | not enforced / null |
| task-stack override | none; the official test command is unchanged |
| wall watchdog | 120,000 ms |
| termination grace | 1,000 ms, then process-group `SIGKILL` |
| aggregate cgroup/swap ceiling | not enforced / null |
| credit class | one local official-case outcome only after valid completion |

The 8 GiB ceiling is separately registered because TL0.7 explicitly forbids
renaming its 4 GiB development or 8 GiB exporter lanes as a CTest policy.
TL0.7.4's retained matrix showed that unchanged default Lean task-stack
reservations crossed 4 GiB while succeeding by 5 GiB. M0 therefore preserves
the official test script instead of injecting `-s`; it records observed peak
RSS separately and makes no claim about aggregate memory or provider sizing.

## 7. Immutable evidence and credit

The runner must reuse TL0.7.2 process-group cleanup and TL0.7.3
completion-last installation. The planned evidence namespace is
`docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m0/` with:

1. preregistration, source, toolchain, platform, lane, run, shard, and
   prelaunch identities;
2. exact raw CTest stdout/stderr;
3. an attempt terminal installed before JUnit or case validation;
4. raw JUnit plus a canonical parsed projection;
5. exactly one immutable case record binding the official case hash, parent
   selection, attempt, terminal, JUnit test, output policy, and outcome;
6. source/harness post-run manifests and generated test artifacts;
7. completion installed last over the exact dependency set; and
8. a generated authority/result summary.

A valid passed completion sets `official_cases=1` and
`official_outcomes=1`. A valid failed test also creates one official outcome,
but never a pass. Launch, preflight, runner, timeout, signal, malformed JUnit,
selection, identity, or evidence failures create no case outcome. Every state
keeps `axeyum_outcomes`, `paired_cells`, `performance_rows`, `complete_axes`,
`satisfied_gates`, and `parity_credit` at zero. Parent-profile completion and
provider credit remain false in every M0 result.

## 8. Required validation

Offline tests must cover at least:

1. upstream/authority/plan/source/toolchain identity drift;
2. missing, extra, duplicate, reordered, or non-member shard cases;
3. parent context/cell/attempt/selection hash drift;
4. command, environment, working-directory, preset, filter, or resource drift;
5. wrong toolchain file, symlink, mode, or aggregate manifest;
6. discovery count/name/command/property mismatch;
7. absent, malformed, duplicate, extra, or wrong-name JUnit tests;
8. JUnit/exit/terminal/case-outcome disagreement;
9. source or sidecar mutation and undeclared generated artifacts;
10. missing raw output, terminal, case, dependency, or completion records;
11. completion-before-case, overwrite, orphan, and hash/byte drift; and
12. any parent-profile, provider, Axeyum, pair, performance, axis, gate, or
    parity credit.

The live test remains opt-in. Normal CI validates committed evidence offline
and must never fetch Lean, construct a harness, or rerun CTest.

## 9. Stop conditions and next slice

Stop and retain the exact incomplete/invalid result if any prerequisite
identity drifts, discovery is not the singleton, the process is not reaped,
the JUnit/case projection is ambiguous, source changes unexpectedly, or the
store cannot install terminal/case/completion in order. Do not silently widen
memory, time, selection, or command semantics; a retry requires a published
R1 plan.

If M0 closes, TL0.6.3 remains partial: 1 of 3,678 cases in one local shard is
not a complete official profile. M1 must expand by a preregistered,
content-identified shard order, reuse the same immutable case schema, and
deduplicate shared selection sets across the 111 declared attempts. TL0.6.4
may classify this case's native Axeyum surface independently; only TL0.6.5 may
form a matched both-system cell.
