# TL0.6.3 M0 R2 plan — use the released toolchain compiler

Status: **preregistered; no R2 harness or test process has run**

Date: 2026-07-22

Parent work:

- [`M0 plan`](lean-u2-official-execution-tl0.6.3-m0-plan-2026-07-22.md)
- [`attempt 001`](lean-u2-official-execution-tl0.6.3-m0-attempt-001-2026-07-22.md)
- [`R1 result`](lean-u2-official-execution-tl0.6.3-m0-r1-result-2026-07-22.md)
- [`TL0.6.3`](lean-system-implementation-plan-2026-07-21.md#tl06-u2-official-test-execution-slices)

## 1. Decision boundary

R2 is one retry of the same registered case, parent selection, official source,
released toolchain, CTest command/filter, 8 GiB per-process address-space
ceiling, 120-second watchdog, explicit CTest/Lean-shell `-j1`, generated-runtime
worker request, default Lean task stack, and declared artifact closure.

It corrects one adapter defect only: remove `LEAN_CC=/usr/bin/cc` from the
generated test wrapper and environment. No replacement `LEAN_CC` is permitted.
The pinned `leanc` must choose its configured bundled compiler and sysroot.
Official Linux release preparation explicitly leaves `LEAN_CC` unset for tests;
`leanc` documents the variable as an override.

The only possible new positive result is one local official-case outcome for
`compile/534.lean`. R2 cannot complete the 3,678-case parent, claim an official
provider, create an Axeyum outcome or pair, publish performance, advance
A0--A11, satisfy G1--G10, or establish Lean parity.

No R2 harness or test process may run until the R1 evidence/result and this plan
are committed and pushed. The R2 implementation must then be committed and
pushed separately before the test process runs.

## 2. Frozen R1 dependency

R2 must validate and retain both earlier attempts:

| Field | Frozen value |
|---|---|
| attempt-001 files / bytes / manifest | 18 / 4,757,134 / `7b8452e0a003a11867d2fc2150c00af99a0a61f41b10238b88a3ed2bb3838065` |
| attempt-001 outcomes | 0 |
| attempt-002 files / bytes / manifest | 23 / 4,778,395 / `7b08bb0a450676db217ba138ccff34dccf9c682c587ea5f25fd6b8bcc0cfecef` |
| attempt-002 terminal / JUnit / completion | `a0d2cef7134a9301458250cc1fa5de360aacbbdc342fbe81e13d962640a0dc20` / `65deb3bef7c2c9910f5763731eda116c7453bc6f11069184a9801226d039852c` / `85d4c1b4b478157d1f54b35c993e559f8ab5fd2f7489dce7b2b842d4d06c9e91` |
| attempt-002 outcome | one local official failure; zero passes and parity credit |
| R1 authority physical / record SHA-256 | `61c7bb015dee1cb767b6c460a08f2c4416a62f1c41e040c817fd5b0d6ea24f8d` / `fe1a61fd0ec3e2fed918d46711cec66644b0980795dfaf80fe9ed401556dfa6e` |

The R2 final authority must count three process attempts. If R2 reaches a
decided outcome, it must count two official outcomes: attempt 002's failure and
attempt 003's result. It must never rewrite the earlier failure into a pass.

## 3. Corrected compiler contract

The lane becomes `official-ctest-local-8g-lean-j1-bundled-cc-v3`. The wrapper
must contain no `LEAN_CC` assignment or export. It keeps exact
`TEST_LEAN_ARGS=(-j1)` and `TEST_LEANI_ARGS=(-j1)` assignments before sourcing
the unmodified official runner.

The evidence must bind:

1. absence of `LEAN_CC` in the wrapper and child environment;
2. pinned `leanc` identity
   `519d91f0c9e94c453d420de1ba9d3221c801e3332d4cfc399fc90931c41c23b2`;
3. bundled compiler identity/path selected by `leanc`, including captured
   verbose compiler/linker command evidence;
4. released-toolchain static `libc++.a` and `libc++abi.a` identities; and
5. no system-package installation, added library path, compiler substitution,
   source edit, or task-stack change.

The source-backed rationale is fixed at Lean commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`:

- [`prepare-llvm-linux.sh`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/script/prepare-llvm-linux.sh#L70-L81)
  leaves test `LEAN_CC` variables empty;
- [`Leanc.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Leanc.lean#L15-L65)
  treats `LEAN_CC` as an override; and
- [`run_test.sh`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/compile/run_test.sh#L17-L38)
  invokes `leanc` for the generated C file.

## 4. Attempt and artifact identities

R2 uses sequence 3, attempt ID `attempt-003`, and a fresh private work/evidence
root. It must not overwrite either earlier evidence root or R1 authority.

The CTest command, case selection, expected output, source/toolchain archives,
four case-output paths, two pass-side CTest logs, optional failure-side
`LastTestsFailed.log`, process closure, immutable installation, and
outcome-sensitive post-run rules remain exactly as R1 defined them.

A pass requires exit zero, exactly four case artifacts, exactly the two
pass-side CTest logs, no failed-list log, original-source replay, and a reaped
process group. A genuine test failure may add one failure outcome only if every
adapter/resource/evidence contract validates. Infrastructure, identity,
artifact, process, or store failure adds no outcome.

## 5. Required offline gates

Before execution, tests must reject:

1. drift in either earlier attempt or the R1 authority;
2. any `LEAN_CC` occurrence in wrapper, spec environment, or child environment;
3. missing/drifted bundled compiler, static C++ archives, or verbose compiler
   selection evidence;
4. absent, duplicated, reordered, or changed `-j1` arrays;
5. any `-s/--tstack`, resource, command, case, or artifact-closure change;
6. attempt/sequence/work/evidence-root reuse;
7. loss or reinterpretation of attempt 002's failed outcome; and
8. parent, provider, Axeyum, pair, performance, axis, gate, or parity credit.

Normal CI remains offline and must never rerun CTest.

## 6. Stop conditions

Stop and retain R2 if any frozen identity, dependency, compiler selection,
process closure, JUnit relation, source/artifact closure, or immutable-store
step fails. Do not install packages, add linker flags, change cases/resources,
or retry again without a separately published R3 plan.

Even if R2 passes, TL0.6.3 remains partial at two observed local outcomes from
a 3,678-case parent, with zero Axeyum outcomes, pairs, performance rows,
complete populations, axes, gates, and parity credit.
