# TL0.6.2 plan — official Lean CI execution-profile derivation

Status: **preregistered; implementation and derived selection counts not yet
observed**

Date: 2026-07-22

Owner: complete Lean-parity documentation/evidence lane

Parent tasks:

- [`TL0.6`](lean-system-implementation-plan-2026-07-21.md#tl06-u2-official-test-execution-slices)
- [`TL0.6.1` registration result](lean-u2-test-authority-2026-07-22.md)
- [complete Lean 4.30 parity contract](lean4-complete-parity-contract-2026-07-22.md)

## 1. Decision boundary

TL0.6.1 froze which tests Lean registers in two configurations. TL0.6.2 must
now derive which of those registered cases each pinned official workflow cell
would attempt. It is a profile-definition milestone, not a test run:

- no official test process is executed;
- no JUnit, pass, fail, duration, RSS, retry, or completion result is claimed;
- no Axeyum source/workflow/runtime behavior is executed;
- no U2 terminal denominator or paired cell is promoted; and
- disabled and commented-out jobs receive no execution credit.

The milestone succeeds only if the dynamic workflow is reduced to an exact,
content-identified set of event contexts, matrix cells, CTest attempts, and
ordered case-selection sets. TL0.6.3 owns actual official execution.

## 2. Frozen primary inputs

All source identities are SHA-256 over bytes at Lean commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`:

| Input | SHA-256 | Role |
|---|---|---|
| `.github/workflows/ci.yml` | `e90ce40c73a73481b61651e1c10762dedabc72f963fd164d395ba9f2eecd1cad` | check-level, labels, event predicates, dynamic matrix, job enablement |
| `.github/workflows/build-template.yml` | `c5db66bb5612c767f3c9b6b45f95e59d0d01f9f25f110cf2f6e462b41ffe6226` | target-stage selection, primary CTest, rebootstrap CTest, stage-3 and benchmark steps |
| `CMakePresets.json` | `31400a143d5bb683395a1f5b9eff09293f974b92764111b92be172833aa45466` | release/reldebug/sanitize test-preset identities |
| `tests/CMakeLists.txt` | `1bc3c6f21b661104361936648823e5f357081d7026a9487f0b4b614d9aa1bca5` | default versus `LAKE_CI=ON` registration semantics |
| `src/stdlib_flags.h` | `4b69268baa96fb217ad805b15fc33410639809fb21b7df2f93371f1004acd5a4` | current-source bootstrap flag identity |
| `stage0/src/stdlib_flags.h` | `4b69268baa96fb217ad805b15fc33410639809fb21b7df2f93371f1004acd5a4` | stage-0 bootstrap flag identity |
| `lean-u2-test-authority-v1.json` | `d7446e7965bac100ac6b5c607cbb7c87b5b80063fc23b3ec998fff2736d5d18e` | exact 3,678/3,723 registered case sets and case identities |

The equal `stdlib_flags.h` contents preregister `TARGET_STAGE=stage1` for this
pin. A future pin with unequal bytes must derive `stage2`; it may not reuse the
current result.

CTest selection follows the upstream command-line contract: `-R` includes
test names matching its regular expression and `-E` excludes matching names.
The used pinned filters are limited to a portable alternation/literal subset;
the implementation must reject unsupported option shapes rather than guess.

## 3. Canonical official-repository event contexts

The target is the official `leanprover/lean4` repository, so the workflow's
`large` predicate is fixed to true. Fork-runner profiles are a separate future
authority. Seventeen contexts cover every semantically distinct reachable
combination of the pinned event/check-level/`lake-ci`/`fast-ci` predicates:

| Context IDs | Event semantics |
|---|---|
| `pr-l0`, `pr-l0-fast`, `pr-l0-lake`, `pr-l0-lake-fast` | pull request without `merge-ci`/`release-ci`; independent `lake-ci` and `fast-ci` switches |
| `pr-l1`, `pr-l1-fast`, `pr-l1-lake`, `pr-l1-lake-fast` | pull request whose selected level is 1; independent Lake/fast switches |
| `pr-l3`, `pr-l3-fast`, `pr-l3-lake`, `pr-l3-lake-fast` | pull request whose selected level is 3; independent Lake/fast switches |
| `merge-group-l1` | merge queue, level 1, not a pull request or push-to-master |
| `push-master-l1` | push to `master`, level 1, `isPushToMaster=true` |
| `nightly-l2` | scheduled official nightly, level 2, normalized nightly version |
| `manual-nightly-l2` | manual nightly release, level 2, separately identified event |
| `release-tag-l3` | pinned official `v4.30.0` release tag, level 3 |

Label combinations that produce the same tuple are aliases, not new profiles:
`release-ci` takes precedence over `merge-ci`; `lake-ci` and `fast-ci` remain
independent booleans. Non-PR events cannot set those label booleans in this
workflow.

Each context must retain event, level, booleans, repository class, version
mode, and a context digest. The implementation must prove the ordered context
set is exact and reject additions, omissions, reordering, or aliases presented
as independent evidence.

## 4. Matrix and attempt derivation

The implementation must evaluate the pinned JavaScript matrix literal and its
two post-processing loops, not hand-copy a simplified matrix. The capture may
use Node to execute only that isolated source fragment under the frozen context
variables. It must never execute arbitrary workflow steps.

For every context and every active literal matrix job, retain one candidate
cell with at least:

- literal order and stable job ID/name;
- resolved `enabled`, `secondary`, `test`, runner `os`, `release`, shell,
  preset, `CMAKE_OPTIONS`, and `CTEST_OPTIONS`;
- resolved `check-rebootstrap`, `check-stage3`, and `test-bench` flags;
- `LAKE_CI`, `USE_LAKE`, target stage, and registration profile;
- state: `disabled`, `packaging-only`, or `ctest`;
- exact disabled/skip reason where applicable; and
- a complete normalized configuration digest.

The pinned matrix currently contains nine active job literals. The commented
Linux LLVM, Linux 32-bit, and WebAssembly blocks are source inventory only and
must not appear as active cells or attempts. The 17 contexts therefore
preregister 153 candidate cells before predicates are evaluated.

An enabled cell with `test=true` owns one primary attempt. A cell with
`check-rebootstrap=true` owns a second, distinct rebootstrap attempt:

- primary attempt: selected `TARGET_STAGE`, matrix preset and
  `CTEST_OPTIONS`, `--output-junit test-results.xml`;
- rebootstrap attempt: fixed `build/stage1`, the matrix preset, **no inherited
  matrix `CTEST_OPTIONS`**, and no JUnit argument in the pinned command.

Stage-3 checks and benchmark targets are retained as non-CTest action flags;
they may not manufacture U2 case attempts. The post-test binary check is also
retained separately from the CTest case set.

## 5. Factored selection sets

The manifest must not duplicate thousands of case IDs per attempt. It must
deduplicate exact ordered selection sets by:

1. TL0.6.1 registration profile (`default` or `full-lake`);
2. normalized supported CTest include/exclude options; and
3. ordered selected case IDs.

Each selection set retains registered count/digest, selected IDs/count/digest,
excluded IDs/count/digest, and its own content digest. Every CTest attempt
references exactly one selection set. Counts must reconstruct from IDs; equal
counts with different IDs are a mismatch.

The implementation must independently verify the portable filter evaluation
against CTest `--show-only=json-v1` over the same registered names during
explicit pinned-upstream verification. Normal CI validates the committed
authority offline.

## 6. Required fail-closed tests

At least these mutation classes must reject:

1. wrong Lean/U2/input identity;
2. missing, duplicate, reordered, or aliased context;
3. active inclusion of a commented job;
4. job-cell omission, duplication, or context/job mismatch;
5. wrong enablement, primary/secondary split, runner, preset, or options;
6. a disabled or packaging-only cell acquiring a CTest attempt;
7. a test cell missing its primary attempt;
8. rebootstrap inheriting the primary `CTEST_OPTIONS` or wrong target stage;
9. stage-3/benchmark flags becoming CTest attempts;
10. unsupported CTest option/filter syntax;
11. selected/excluded case membership, order, count, or digest mutation;
12. attempt-to-selection-set or profile mismatch;
13. hand-entered pass/fail/duration/resource/completion outcomes; and
14. promotion of U2 to `complete_authority` or creation of terminal paired
    cells from profile derivation alone.

## 7. Output and stop conditions

Planned artifacts:

- `docs/plan/lean-u2-official-ci-profiles-v1.json`;
- `docs/plan/generated/lean-u2-official-ci-profiles.json`;
- `docs/plan/generated/lean-u2-official-ci-profiles.md`;
- `scripts/gen-lean-u2-official-ci-profiles.py`; and
- `scripts/tests/test_lean_u2_official_ci_profiles.py`.

Stop and retain TL0.6.2 as partial if any of these occurs:

- the workflow fragment cannot be isolated without evaluating untrusted steps;
- an active job, predicate, option, or stage cannot be reproduced exactly;
- Python and CTest selection membership differ;
- a context is reachable but not representable in the frozen schema;
- a required source/input identity drifts; or
- any result field could be mistaken for an actual completed test outcome.

If the derivation closes, TL0.6.2 becomes done but U2 remains
`bounded_profile`. The next authorized observation is TL0.6.3's retained
official execution, not an Axeyum parity claim.
