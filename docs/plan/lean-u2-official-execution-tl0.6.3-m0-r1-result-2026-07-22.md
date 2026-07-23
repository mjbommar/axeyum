# TL0.6.3 M0 R1 result — retained local official-case failure

Status: **complete bounded result; one local official failure outcome; zero parity credit**

Date: 2026-07-22

Authority:

- [`lean-u2-official-execution-tl0.6.3-m0-v1.json`](lean-u2-official-execution-tl0.6.3-m0-v1.json)
- [generated summary](generated/lean-u2-official-execution-tl0.6.3-m0.md)
- [attempt-002 evidence](evidence/lean-u2-official-execution-tl0.6.3-m0/)
- [attempt-001 retained failure](evidence/lean-u2-official-execution-tl0.6.3-m0-attempt-001-failed/)
- [`R1 plan`](lean-u2-official-execution-tl0.6.3-m0-r1-plan-2026-07-22.md)
- [`R1 Git-mode amendment`](lean-u2-official-execution-tl0.6.3-m0-r1-git-mode-amendment-2026-07-22.md)

## 1. Bounded verdict

R1 closed the execution/evidence contract and retained one decided **failed**
outcome for the exact official CTest registration `compile/534.lean`. This is
not a Lean semantic rejection: generated C was produced, but the adapter forced
`leanc` through `/usr/bin/cc`, whose linker could not find static `libc++` and
`libc++abi`. The local shard is complete at 1/1 with zero passes; the parent
release-tag Linux-release selection is only 1/3,678 observed and remains
incomplete.

The result does not reproduce an official provider, run Axeyum, create a
matched pair or performance row, advance any A0--A11 axis, satisfy any G1--G10
gate, or establish Lean parity.

## 2. Exact retained result

| Field | Value |
|---|---|
| implementation revision | `1a2e7d3aa59710ba4c5dce7fe7f90f86db4841e4` |
| attempt | `attempt-002`, sequence 2 |
| lane | `official-ctest-local-8g-lean-j1-v2` |
| case | `compile/534.lean` |
| outcome | `failed` |
| terminal | exited 8; no signal; watchdog false; group reaped |
| wall / peak RSS | 455 ms / 21,360,640 bytes |
| generated case artifact | `534.lean.c`, 9,713 bytes, SHA-256 `fa221b7899387fb8b3413bdae6bd63e87303added2ba4378466668f0a9441a53` |
| R1 evidence | 23 files / 4,778,395 bytes |
| evidence manifest | `7b08bb0a450676db217ba138ccff34dccf9c682c587ea5f25fd6b8bcc0cfecef` |
| terminal / JUnit / completion records | `a0d2cef7134a9301458250cc1fa5de360aacbbdc342fbe81e13d962640a0dc20` / `65deb3bef7c2c9910f5763731eda116c7453bc6f11069184a9801226d039852c` / `85d4c1b4b478157d1f54b35c993e559f8ab5fd2f7489dce7b2b842d4d06c9e91` |
| two-attempt authority | `fe1a61fd0ec3e2fed918d46711cec66644b0980795dfaf80fe9ed401556dfa6e` |

The authority retains both process attempts: attempt 001 has zero outcomes;
attempt 002 has one official failure outcome. Credits are one official case,
one official outcome, one official failure, zero official passes, and zero for
every non-official/parity field.

## 3. Cause and source confirmation

The retained wrapper exported `LEAN_CC=/usr/bin/cc`. Lean's `leanc` explicitly
uses `LEAN_CC` as a compiler override; otherwise it uses its configured bundled
compiler. The pinned Linux distribution preparation explicitly says not to set
`LEAN_CC` for tests, while the official compile runner invokes `leanc` after
generating C. These are upstream source facts, not an inferred package fix:

- [`src/Leanc.lean`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Leanc.lean#L15-L65)
- [`script/prepare-llvm-linux.sh`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/script/prepare-llvm-linux.sh#L70-L81)
- [`tests/compile/run_test.sh`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/tests/compile/run_test.sh#L17-L38)

The released toolchain already contains `lib/libc++.a` and
`lib/libc++abi.a`. A bounded post-result diagnostic reused the retained
9,713-byte C file:

| Link control | Exit | Observation |
|---|---:|---|
| `LEAN_CC=/usr/bin/cc leanc ...` | 1 | system `ld.bfd` reports both static libraries missing |
| `env -u LEAN_CC leanc ...` | 0 | bundled toolchain compiler emits an executable |

The failed-control stderr SHA-256 is
`87f7f6f48c15bdfd4dfd933f8182a23bd178d7e89f010ee0eb3f10b3e10bec2d`;
the successful-control stderr SHA-256 is
`47fb370ded5bac9c1f71c37e5e22292b6449c27ce4b3c281f7009629a1985528`.
These post-hoc diagnostics receive no official outcome or parity credit and do
not reinterpret attempt 002.

## 4. Contract corrections proved by R1

R1 did correct and validate the preregistered defects:

1. CTest ran with one worker, the Lean shell received the supported `-j1`
   arrays, and generated runtime workers remained requested through
   `LEAN_NUM_THREADS=1` without claiming an OS thread ceiling.
2. The three failure-side CTest operational logs were declared and retained;
   no undeclared source artifact appeared.
3. New records used the immutable store's UTF-8 canonical serializer, while
   attempt 001's physical UTF-8 bytes and legacy seals validated unchanged.
4. Live evidence was `0444`; offline validation used Git mode `100644` plus
   exact bytes, seals, and manifests.

## 5. Next boundary

The separately preregistered
[`R2 plan`](lean-u2-official-execution-tl0.6.3-m0-r2-plan-2026-07-22.md)
removes only the unsupported `LEAN_CC` override. It preserves this result as an
official failure outcome and still permits at most one additional local
official-case outcome. No silent retry is authorized.
