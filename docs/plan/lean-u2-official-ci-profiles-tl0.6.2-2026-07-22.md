# TL0.6.2 result — official Lean CI execution profiles

Status: **complete as a profile derivation; no test execution or parity result**

Date: 2026-07-22

Parent:

- [preregistered TL0.6.2 plan](lean-u2-official-ci-profiles-tl0.6.2-plan-2026-07-22.md)
- [TL0.6.1 registration authority](lean-u2-test-authority-2026-07-22.md)
- [complete Lean 4.30 parity contract](lean4-complete-parity-contract-2026-07-22.md)

Machine-readable evidence:

- [official CI profile authority](lean-u2-official-ci-profiles-v1.json)
- generated [Markdown](generated/lean-u2-official-ci-profiles.md) and
  [JSON](generated/lean-u2-official-ci-profiles.json) summaries
- generator [`scripts/gen-lean-u2-official-ci-profiles.py`](../../scripts/gen-lean-u2-official-ci-profiles.py)
- contract tests
  [`scripts/tests/test_lean_u2_official_ci_profiles.py`](../../scripts/tests/test_lean_u2_official_ci_profiles.py)

## 1. Verdict

TL0.6.2 closes the question “which official workflow profiles would select
which registered Lean tests?” for the pinned Lean v4.30.0 source. It does not
answer whether any test passes, whether Axeyum implements the selected surface,
or whether the two systems agree.

The exact bounded result is:

- 17 semantically distinct official-repository event contexts;
- nine active matrix job literals and 153 context/job candidate cells;
- 85 enabled test cells, 53 disabled cells, and 15 enabled packaging-only
  cells;
- 111 declared CTest attempts: 85 primary and 26 separately derived
  rebootstrap attempts;
- eight exact factored case-selection sets; and
- zero official executions, zero completed official cases, zero Axeyum
  executions, and zero paired cells.

U2 therefore remains `bounded_profile`. No U2 terminal denominator, A0-A11
axis, G1-G10 gate, or unqualified Lean-parity claim changes state.

## 2. Source-first evidence order

The input identities, context closure, derivation rules, mutation classes, and
stop conditions were committed and pushed as `4038dcf3` before the first
derived profile counts were observed. The subsequent capture reproduced every
preregistered source identity at Lean commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`:

- `.github/workflows/ci.yml` supplies check-level, event, label, matrix, and
  enablement semantics;
- `.github/workflows/build-template.yml` supplies stage selection and the
  primary/rebootstrap CTest command shapes;
- `CMakePresets.json` supplies `release`, `reldebug`, and `sanitize` test
  presets;
- `tests/CMakeLists.txt` supplies default versus `LAKE_CI=ON` registration;
  and
- equal `src/stdlib_flags.h` and `stage0/src/stdlib_flags.h` bytes select
  `TARGET_STAGE=stage1` at this pin.

The generator extracts and executes only the matrix-construction JavaScript
fragment under frozen input variables. It does not execute a workflow step,
build Lean, invoke a test, or ingest an outcome. Commented Linux LLVM, Linux
32-bit, and WebAssembly blocks remain source inventory and do not become active
jobs.

## 3. Derived workflow semantics

The 17 contexts preserve distinctions that are operationally relevant even
when the selected case set happens to be equal:

- pull requests at levels 0, 1, and 3 retain independent `lake-ci` and
  `fast-ci` switches;
- merge-group level 1 and push-to-`master` level 1 remain separate because
  their enablement predicates differ;
- scheduled nightly, manual nightly, and release-tag contexts remain separate
  event identities; and
- fast/non-fast contexts retain different runner/configuration identities even
  where they select the same registered names.

An enabled `test=true` cell owns one primary attempt. A cell with
`check-rebootstrap=true` also owns a distinct rebootstrap attempt. Primary
attempts retain the matrix preset, filter, target stage, and JUnit shape.
Rebootstrap attempts use `build/stage1`, retain only the preset, deliberately
do not inherit matrix `CTEST_OPTIONS`, and have no JUnit argument in the pinned
command. Stage-3 checks, benchmark targets, packaging cells, and post-test
binary checks remain separately recorded actions; none manufacture CTest case
attempts.

The generated [context table](generated/lean-u2-official-ci-profiles.md#context-matrix)
is the compact review surface. Its “selected occurrences” column counts a case
again for every declared attempt; it is neither a unique denominator nor a
pass count.

## 4. Exact selection corrections

Applying the pinned CTest filters to the TL0.6.1 registered names produces
eight unique ordered selection sets:

| Registration | Filter | Registered | Selected | Excluded |
|---|---|---:|---:|---:|
| default | none | 3,678 | 3,678 | 0 |
| full-Lake | none | 3,723 | 3,723 | 0 |
| default | `-E foreign` | 3,678 | 3,678 | 0 |
| full-Lake | `-E foreign` | 3,723 | 3,723 | 0 |
| default | `-E elab_bench/big_do` | 3,678 | 3,677 | 1 |
| full-Lake | `-E elab_bench/big_do` | 3,723 | 3,722 | 1 |
| default | sanitizer exclusion | 3,678 | 3,477 | 201 |
| full-Lake | sanitizer exclusion | 3,723 | 3,477 | 246 |

Two details correct plausible but false shortcuts:

1. Linux release's `-E foreign` is a no-op over the registered names at this
   pin; preserving the filtered selection as a distinct configuration does not
   invent an excluded case.
2. The sanitizer selection is byte-identical between default and full-Lake.
   Its filter excludes all 45 full-Lake-only Lake cases, so both profiles select
   the same ordered 3,477 IDs even though their registered and excluded counts
   differ.

The selected and excluded ID arrays, counts, order, and SHA-256 digests are
retained in the machine authority. Equal counts with unequal identities cannot
pass validation.

## 5. Independent checks

The implementation has two validation layers:

1. Python reconstructs every context, cell, command, selection membership,
   digest, and no-outcome invariant from the committed authority.
2. Explicit upstream verification creates a synthetic CTest project containing
   the exact registered names and asks CTest `--show-only=json-v1` to apply each
   retained `-R`/`-E` filter. All eight ordered memberships agree.

The 13 focused contract tests cover the fourteen preregistered mutation
classes, including source drift, context/cell closure, commented jobs,
disabled/packaging attempts, missing/spurious phases, rebootstrap filter/stage
drift, unsupported CTest options, selection mutation, and outcome/terminal
credit. The normal documentation gates validate the committed authority
offline; the upstream and CTest reproductions remain explicit stronger checks.

Reproduction:

```sh
python3 -m unittest scripts.tests.test_lean_u2_official_ci_profiles
python3 scripts/gen-lean-u2-official-ci-profiles.py --check
python3 scripts/gen-lean-u2-official-ci-profiles.py --verify-ctest
python3 scripts/gen-lean-u2-official-ci-profiles.py --verify-upstream references/lean4
```

## 6. Assurance boundary and handoff

This result is configuration authority, not execution authority. In
particular, it does not establish executable identity, build success, runner
availability, resource compliance, CTest completion, JUnit/log integrity,
case outcome, native Axeyum coverage, or both-system equivalence.

TL0.6.3 is the next observation-producing slice. It must first join TL0.7's
resource/checkpoint policy, then retain official executable, configuration,
environment, resource, attempt, completion, JUnit, log, and artifact identities
per profile. TL0.6.4 can independently classify the native Axeyum surface and
owner for every selected case. Only TL0.6.5 may register matched native runs,
and only TL0.6.6 may promote U2 after every declared profile and case closes.
