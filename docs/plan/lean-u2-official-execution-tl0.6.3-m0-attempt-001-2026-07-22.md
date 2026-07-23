# TL0.6.3 M0 attempt 001 — retained resource-adapter failure

Status: **failed incomplete; no official-case outcome and no completion**

Date: 2026-07-22 (local) / 2026-07-23 UTC

Parent plan:
[`lean-u2-official-execution-tl0.6.3-m0-plan-2026-07-22.md`](lean-u2-official-execution-tl0.6.3-m0-plan-2026-07-22.md)

Implementation revision:
`bc59fda54a2b6d7aa253173e5203c0aa4c0461ca`

Retained evidence:
[`evidence/lean-u2-official-execution-tl0.6.3-m0-attempt-001-failed/`](evidence/lean-u2-official-execution-tl0.6.3-m0-attempt-001-failed/)

## 1. Bounded result

The preregistered singleton was discovered and launched through the exact
official `compile/534.lean` registration, but it did not produce a valid M0
case outcome. CTest exited `8`; the retained JUnit has one failed testcase;
and the official runner reports that Lean aborted while compiling the source:

```text
libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread
```

The attempt terminal was installed before JUnit interpretation. The process
group was reaped with no live non-zombie member. The subsequent source closure
also found three undeclared CTest preset artifacts under
`build/release/Testing/Temporary`. The runner therefore stopped before
`post.json`, `case.json`, or `completion.json` could be installed.

Postmortem validation found a third, latent adapter defect before R1: the
runner's private canonical-JSON helper used ASCII escaping while the accepted
immutable installer uses UTF-8 canonical JSON. The frozen source manifest has
two official non-ASCII test paths (`utf8Path.lean.英語` and `utf8英語.lean`), so
the attempt's physical records are valid installer-canonical bytes but the
runner's loader would have rejected them during final closure. No failed byte
is rewritten; R1 must validate this namespace with its exact legacy seal rule
while using the single accepted UTF-8 canonical rule for all new records.

This is a resource-adapter/evidence-contract failure, not evidence that the
official Lean case is semantically failing. It creates **zero** official case
outcomes, parent-profile completions, provider completions, Axeyum outcomes,
matched cells, performance rows, axes, gates, or parity credit.

## 2. Exact retained observation

| Field | Value |
|---|---|
| case | `compile/534.lean` |
| implementation | `bc59fda54a2b6d7aa253173e5203c0aa4c0461ca` |
| spec record | `e5aa1a0c8f152c1bec5de80844cee791e09a35b866ee8b9397ee6549d409f7b2` |
| terminal record | `93d033a92b1ba13631cf754ec717cf6058afb5a76e4a617eab1891331d93a55e` |
| terminal | `exited` / code `8` / signal null |
| elapsed | 342 ms |
| observed peak RSS | 21,610,496 bytes |
| JUnit record | `03b4aec0d34fdbbadd9acae8327934d7d90da87593ae74ecd49cc01f0069f687` |
| JUnit | one test / one failure / `compile/534.lean` |
| raw stdout | 612 bytes / `c01ad3909b8218378f63aad27b16bbc1fb898103fed48b14f9692e0612dd997f` |
| raw stderr | 27 bytes / `18e00877dc1071c85cd4f479d451bebeef8309022e46cf8c63b0bed5151984a4` |
| raw JUnit | 674 bytes / `74b763a021ea89bc86eeab3c873485f4d62fddcd87499edd901f8d1ff460a77b` |
| evidence | 18 files / 4,757,134 bytes |
| evidence manifest | `7b8452e0a003a11867d2fc2150c00af99a0a61f41b10238b88a3ed2bb3838065` |

The evidence manifest digest is domain-separated with
`axeyum-lean-u2-official-execution-attempt-evidence-v1`. The retained CTest
temporary logs are byte-identical copies of the three generated files from
the isolated source tree.

## 3. Root cause

Attempt 001 set `LEAN_NUM_THREADS=1`, but that does not constrain the `lean`
command-line shell's own task manager. In pinned Lean 4.30:

- [`Lean/Shell.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Lean/Shell.lean)
  initializes `ShellOptions.numThreads` from native hardware concurrency and
  changes it through `-j/--threads`;
- [`src/util/shell.cpp`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/util/shell.cpp)
  constructs the shell task manager from that parsed option; and
- [`src/runtime/thread.cpp`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/runtime/thread.cpp)
  reserves a 1 GiB default stack per 64-bit Lean thread.

The retained platform record reports 24 online CPUs. The evidence therefore
supports the inference that the shell retained its 24-thread native default,
making the supposed one-Lean-worker 8 GiB lane internally inconsistent. The
attempt does not include `strace`, so it does not claim an exact count of
successful stack mappings before the failure.

Lean's official test documentation explicitly defines `TEST_LEAN_ARGS` and
`TEST_LEANI_ARGS` as the supported Bash arrays for adding arguments to the
compiler and interpreter invocations:
[`tests/README.md`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/README.md).

Separately, CTest's preset contract associates the test preset with its
configure preset and inferred binary directory. CMake 4.2 did execute the
explicit `--test-dir` singleton harness, as retained stdout and JUnit prove,
but wrote operational logs under the release preset's
`build/release/Testing/Temporary` path. See the official
[`ctest(1)`](https://cmake.org/cmake/help/latest/manual/ctest.1.html) and
[`cmake-presets(7)`](https://cmake.org/cmake/help/latest/manual/cmake-presets.7.html)
contracts.

The canonicalization mismatch is local to the M0 adapter. The immutable store
used its already accepted UTF-8 serializer, so it did not corrupt or replace
any retained record. The bug was the runner's duplicate serializer/loader and
would have prevented a completion even if the case process had passed.

## 4. Correction boundary

No failed evidence byte will be rewritten and attempt 001 will never be
promoted into a case or completion. The source-first
[`R1 plan`](lean-u2-official-execution-tl0.6.3-m0-r1-plan-2026-07-22.md)
owns the only permitted retry: explicit shell `-j1` through the supported
test arrays, one canonical serializer, a corrected resource record, declared
CTest temporary artifacts, a fresh work/evidence root, sequence 2, and
unchanged zero-credit boundaries.
