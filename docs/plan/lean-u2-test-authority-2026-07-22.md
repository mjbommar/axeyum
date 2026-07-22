# Lean U2 official-test registration authority

Status: **bounded registration authority complete; U2 execution and parity
authority incomplete**

Date: 2026-07-22

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`

Machine-readable source:
[`lean-u2-test-authority-v1.json`](lean-u2-test-authority-v1.json)

Generated summaries:
[Markdown](generated/lean-u2-test-authority.md) and
[JSON](generated/lean-u2-test-authority.json)

Parent contract:
[`lean4-complete-parity-contract-2026-07-22.md`](lean4-complete-parity-contract-2026-07-22.md)

## 1. Bounded verdict

The pinned upstream test selection is now reproducible from Lean's executable
registration semantics instead of a raw file count:

- the default `LAKE_CI=OFF` configuration registers **3,678** CTest cases;
- `LAKE_CI=ON` registers **3,723** cases;
- the default selection is a strict subset, with **45** full-Lake-only cases;
- the full selection contains 3,639 pile cases, 31 non-Lake test directories,
  52 Lake directories, and one serial lint case; and
- its output policies partition into 2,099 empty-output, 1,480 exact-output,
  60 ignored-output, and 84 script-defined cases.

This closes the registration-denominator part of U2 for two configurations. It
does **not** establish complete U2 authority or Lean parity. The capture records
zero official executions, zero Axeyum executions, and zero paired cells.

## 2. Primary upstream semantics

The authority is derived from pinned primary sources:

- Lean's
  [`tests/README.md`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/README.md)
  distinguishes a directory test from a pile test, defines success as a zero
  runner exit, and documents `.out.expected`, `.out.ignored`, initialization,
  before/after, argument, and expected-exit sidecars.
- Pinned
  [`tests/CMakeLists.txt`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/CMakeLists.txt)
  is the selection authority. It registers pile globs only when a test runner
  exists, excludes `run_test`/`run_bench` names and `<file>.no_test`, registers
  directory runners as one case, and switches the Lake selection with
  `LAKE_CI`.
- Pinned
  [`ci.yml`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/.github/workflows/ci.yml)
  dynamically chooses platforms, presets, exclusions, release/check levels,
  rebootstrap, stage-3, and benchmark work.
- Pinned
  [`build-template.yml`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/.github/workflows/build-template.yml)
  runs CTest against the selected target stage and may perform a second
  post-rebootstrap stage-1 CTest run.
- Pinned
  [`CMakePresets.json`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/CMakePresets.json)
  defines release, debug, release-with-assertions, sanitizer, and
  sanitizer-plus-debug test presets.

These are distinct layers. `tests/CMakeLists.txt` answers which cases a given
configuration registers. The workflows answer which registered subset is
actually attempted on a platform and event. JUnit/log evidence answers what
ran and passed. Only a matched Axeyum run can answer parity.

## 3. Exact derivation and content closure

The capture tool exports the pinned `tests/` and `doc/examples/` Git trees into
a temporary directory, configures a minimal CMake harness twice, and consumes
CTest's own JSON-v1 registration view. Host paths are normalized to explicit
tokens; no test is executed during capture.

Every full-Lake case retains:

- its exact CTest name and ordered profile membership;
- normalized command and CTest properties;
- test kind and family;
- primary path and SHA-256;
- every same-prefix sidecar path;
- declared output policy and expected-output path when applicable;
- a content-identified, deliberately over-approximating support subtree; and
- a domain-local case digest.

The population also retains all **7,004** Git-tracked files under the two
content roots: 6,931 under `tests/` and 73 under `doc/examples/`. File mode,
Git blob identity, byte length, and SHA-256 are recorded. This over-approximation
prevents an unlisted helper from changing without changing the authority;
future dependency tracing may narrow per-case closures without weakening the
current content identity.

Pile accounting closes independently:

| Classification | Count |
|---|---:|
| Declared pile glob candidates | 3,660 |
| Registered pile cases | 3,639 |
| Excluded by `.no_test` | 7 |
| Excluded runner names | 3 |
| Benchmark-only candidates with no test runner | 11 |

The complete excluded path/reason set is retained in the machine-readable
authority. Equal totals cannot conceal a changed selection because each
profile additionally has an ordered registration digest.

## 4. Why the two captured profiles are not the official CI denominator

At this pin, the workflow has check levels 0 through 3. Its active jobs include
Linux release, Linux Lake, cached Linux Lake, Linux release-with-assertions,
Linux sanitizer, macOS x86-64, macOS AArch64, Windows x86-64, and Linux AArch64.
Their enablement and test behavior differ:

- Linux release excludes `foreign` and does not test at check level 0;
- release-with-assertions and sanitizer jobs start at level 2 and have distinct
  exclusion expressions;
- macOS x86-64 is a Tier-2 packaging job with `test: false` at this pin;
- macOS AArch64 tests from level 1, while Windows and Linux AArch64 test from
  level 2; and
- `LAKE_CI=ON` is added only when the `lake-ci` pull-request label is present.
  A release's level 3 does not by itself turn it on.

The workflow also chooses stage 1 versus stage 2 from bootstrap inputs, can run
stage-3 equivalence and benchmarks, and repeats an unfiltered stage-1 CTest run
after rebootstrap for selected Linux jobs. Consequently, neither “3,678” nor
“3,723” is by itself the official release-CI execution denominator. The next
milestone must evaluate the workflow predicates and CTest filters into exact,
content-identified execution profiles.

## 5. Reproduction and gates

Normal validation is offline and does not require an upstream checkout:

```sh
python3 -m unittest scripts.tests.test_lean_u2_test_authority
python3 scripts/gen-lean-u2-test-authority.py --check
```

Reproduce the capture from a clean checkout at the exact pinned commit:

```sh
python3 scripts/gen-lean-u2-test-authority.py \
  --verify-upstream references/lean4
```

Refresh is an explicit maintainer operation because it rewrites the committed
authority and generated summaries:

```sh
python3 scripts/gen-lean-u2-test-authority.py \
  --capture-upstream references/lean4
```

The capture uses an isolated Git archive, so CMake-generated environment
wrappers do not alter the source checkout. It rejects a wrong commit or tracked
upstream modifications.

## 6. Remaining U2 execution sequence

1. Derive every active official CI event/check-level/platform/preset/filter,
   target-stage, rebootstrap, retry, resource, and completion identity.
2. Retain official JUnit plus command, environment, executable, log, duration,
   resource, artifact, and attempt evidence for every derived profile.
3. Classify each case by the native Axeyum surface it requires: parser/macro,
   elaborator, tactic/meta, module/Lake, server, compiler/runtime, FFI, or
   checker-only.
4. Execute the same normalized cases as those native surfaces become real;
   record not-run and typed declines rather than substituting official Lean.
5. Publish per-case overlap, official-only, Axeyum-only, semantic-mismatch,
   unadjudicated, invalid-run, and resource outcomes.
6. Promote U2 to `complete_authority` only when the complete declared profile
   matrix and both-system outcomes satisfy the terminal contract.

Until all six steps close, this artifact is bounded A0 measurement progress,
not K2-K6 or complete-parity credit.
