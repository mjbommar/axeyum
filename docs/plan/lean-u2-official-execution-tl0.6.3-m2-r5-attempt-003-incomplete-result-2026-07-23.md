# Lean U2 TL0.6.3 M2 R5 attempt-003 incomplete result

Status: **selected attempt consumed; 64 diagnostic passes; zero credit pending
source-first diagnostic closure**

Date: 2026-07-23

Parents:
[R5 plan](lean-u2-official-execution-tl0.6.3-m2-r5-attempt-003-plan-2026-07-23.md)
and [implementation](lean-u2-official-execution-tl0.6.3-m2-r5-attempt-003-implementation-2026-07-23.md).

## 1. Authorized invocation

Clean pushed revision `c445027d04c08d6c72803710d9c4e6640dc4bc5c`
passed offline and direct-stack preflight. The completion-grade 32 GiB fanout
control exited 0 in 548 ms, printed the exact success line, retained eight
files / 8,562 bytes, and authorized selected execution with completion
`19e6072eff957659bb70c5ef044ead11777b002210cd9708ce7366cc3763cb52`.
Its last distinct process sample observed 14 threads, 19,927,060,480-byte
`VmPeak`, 16,638,775,296-byte `VmSize`, and 496,447,488-byte `VmRSS`.

Attempt 003 then ran exactly once from the same revision, control digest, and
frozen roots. The selected terminal is clean exit 0 after 78,449 ms, direct-
child peak RSS 19,873,792 bytes, no signal/watchdog, child reaped, and no live
group member. Terminal record is
`c108edac40fae92e61c4c35eeb5264903c67b42e86a8a0e7d6e5c5590e69b47f`.

## 2. Diagnostic outcome and fail-closed stop

JUnit record `38aa3325b66b41ff9333dcffd9ecc6fe4caf1f8877d7f9470b1a6fd9c52a6302`
contains exactly 64 enabled, non-skipped rows: 64 passes and zero failures.
All 64 sealed case records were installed. These rows are diagnostic only.

Post capture then compared the live source tree with the preregistered exact
124 generated paths and stopped before post/projection/completion. The actual
all-pass run has 123 generated paths and no extras. Its sole missing path is:

```text
build/release/Testing/Temporary/LastTestsFailed.log
```

CTest omits that failure-only log when every row passes. The two present logs
are `CTestCostData.txt` (2,370 bytes) and `LastTest.log` (73,522 bytes). No
official source path changed.

The generated tree totals 950,304,539 bytes: 66 outcome/log payloads / 83,858
bytes are retention candidates, 56 reproducible C/executable intermediates /
950,219,754 bytes are metadata-only, and the 927-byte wrapper remains the one
harness artifact. Its ordered diagnostic digest is
`75feb6d5520aec0286b1dac83bbd3a5047e93f238eb5c3b986c48136e00c1c67`.

## 3. Frozen incomplete evidence and credit

The pre-post evidence root contains 83 files / 5,078,773 bytes: fixed records,
harness artifacts, raw discovery/stdout/stderr/JUnit, terminal/JUnit, and all
64 cases. Domain digest `r5-incomplete-evidence-v1` is
`10d3d3c5dc565331b8a2b3723d0e1155180386017a5ee1ccb17306df8cc9369d`.
It intentionally has no post, projection, or completion.

Attempt 003 is consumed. Because the exact generated-path contract failed,
R5 grants zero official outcomes/shard completions and zero provider, Axeyum,
pair, performance, population, axis, gate, or parity credit. The 64 passes may
not be promoted retroactively.

## 4. Source-first diagnostic closure plan

Before any append, this incomplete root and document must be committed and
pushed. A separately implemented zero-process closure may then:

1. revalidate the exact control, fixed evidence, terminal, JUnit/cases, source
   immutability, and live 123-row generated tree;
2. classify `LastTestsFailed.log` as conditionally absent iff JUnit failures are
   zero, while still requiring it for any failing row;
3. retain exactly the 66 payloads, bind 56 metadata-only rows, retain the
   wrapper only through the existing harness artifact, and append a diagnostic
   post plus zero-credit completion last;
4. preserve all 64 rows as diagnostic and mark attempt 003 invalid for selected
   outcome credit.

No process, selected retry, result projection, or outcome promotion is
authorized by this closure. A future selected attempt requires a new
source-first attempt-004 plan with conditional-log semantics frozen before
execution.
