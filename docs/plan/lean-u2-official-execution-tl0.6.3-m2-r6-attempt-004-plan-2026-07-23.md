# Lean U2 TL0.6.3 M2 R6 attempt-004 plan

Status: **preregistered; no R6 implementation, control, harness, discovery, or
selected process exists**

Date: 2026-07-23

Parents:
[R5 incomplete result](lean-u2-official-execution-tl0.6.3-m2-r5-attempt-003-incomplete-result-2026-07-23.md)
and [R5 diagnostic closure](lean-u2-official-execution-tl0.6.3-m2-r5-diagnostic-closure-result-2026-07-23.md).

## 1. Decision boundary

R6 corrects exactly one artifact-contract defect exposed by R5: CTest creates
`LastTestsFailed.log` only when at least one JUnit row fails. It retains the
already-qualified 32 GiB address-space lane, universal 512 MiB Lean stack, one
CTest worker, one-hour watchdog, exact 64-case shard/command/order, tiered
payload store, completion-last publication, and all non-local credit zeros.

No R6 implementation, control, harness, discovery, or selected process may run
until this plan is committed and pushed. Implementation/offline tests and their
documentation checkpoint must be committed and pushed separately. One fresh
completion-grade fanout control from that clean remote-equal revision must pass
before exactly one selected attempt-004 process is authorized.

## 2. Frozen history and non-promotion

R5's control passed and selected attempt 003 exited cleanly with 64/64 JUnit
passes. Its unconditional 124-path contract rejected the absent failure-only
log before post/projection/completion. The later zero-process closure appended
68 diagnostic files and completion
`2d5d43a7787ccf4333b152be8794a12b45edc7527e32732abb2cf1cce1ffce3c`,
but it intentionally grants zero outcomes. Attempt 003 is consumed, invalid,
closed, and cannot be retried or retroactively promoted.

R6 must validate the exact R5 raw and diagnostic completion identities before
constructing any new root. No R5 byte may be changed or copied as an R6
outcome. The new attempt starts from the original pinned source archive and
released toolchain through fresh capture/preflight.

## 3. Frozen identity and resource envelope

| Field | Frozen value |
|---|---|
| run ID | `tl0.6.3-m2-release-linux-shard-0001-v5` |
| selected attempt / sequence | `attempt-004` / 4 |
| shard | unchanged membership shard `0001`, offsets `[64,128)`, exact 64 cases |
| implementation | full clean pushed R6 invocation revision |
| control root | new `/home/mjbommar/.cache/axeyum-tl063-m2-r6-control-<short-revision>` |
| private work root | new `/home/mjbommar/.cache/axeyum-tl063-m2-r6-<short-revision>` |
| evidence root | `docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m2-shard-0001-r6-attempt-004/` |
| selected process count | zero before invocation; exactly one if authorized |
| CTest | exact harness, `-j1`, one-hour watchdog |
| memory | 32 GiB `RLIMIT_AS` = 34,359,738,368 bytes per control/selected process |
| stack | universal `LEAN_STACK_SIZE_KB=524288` |

The corrected 274-byte nine-dedicated-task control source and exact
`R4_FANOUT_OK|tasks=9|sum=36` success line remain byte-identical. R6 creates a
fresh completion-grade control root because the selected runner is bound to a
new implementation revision. Control failure blocks R6 before selected
discovery and does not consume attempt 004. Once selected discovery or CTest
exists, attempt 004 is consumed and cannot retry.

## 4. Conditional generated-artifact contract

The 121 unconditional generated paths remain exact: 64 per-case
`.out.produced` captures, 56 reproducible `.c`/`.out` intermediates, and the
existing wrapper path. Two CTest logs are also unconditional:

```text
build/release/Testing/Temporary/CTestCostData.txt
build/release/Testing/Temporary/LastTest.log
```

The third CTest path is conditional:

```text
build/release/Testing/Temporary/LastTestsFailed.log
```

After terminal and exact 64-row JUnit validation, R6 requires that path if and
only if `official_failures > 0`. Therefore the only admitted closure shapes
are:

| JUnit state | Generated rows | Retained payloads | Metadata-only | Existing wrapper |
|---|---:|---:|---:|---:|
| 64 passes / 0 failures | 123 | 66 | 56 | 1 |
| at least 1 failure, no skipped/disabled row | 124 | 67 | 56 | 1 |

Absence of either unconditional log, presence of the failure log on all-pass
JUnit, absence of the failure log on any-failure JUnit, an extra path, source
mutation, row-order drift, or count/digest/store mismatch invalidates the
attempt. Classification occurs only after JUnit; filesystem observation never
chooses the semantic branch by itself.

## 5. Selected publication and credit

The store order remains fixed records and raw payloads, 64 case records, post,
projection, then completion last. A valid post binds the JUnit-selected
generated-path set, full/retained/metadata digests, and the conditional-log
predicate. A valid projection credits exactly the 64 local official outcomes
and one completed local physical shard, preserving pass/failure direction.

Parent profile, official provider, Axeyum, paired-cell, performance,
complete-population, complete-axis, satisfied-gate, and parity counters remain
zero. Control evidence, R5 diagnostic rows, or a partial R6 store receive no
outcome credit. This single shard cannot establish full U2 or Lean 4 parity.

## 6. Gates and stop conditions

Offline tests must cover exact R1-R5 history; attempt/run/root freshness;
unchanged resource/source/shard/command identity; both conditional-log branches;
missing/extra/inverted log mutations; JUnit pass/failure/skipped/disabled
mutations; generated-path order and digest drift; completion-last conflicts;
control success/failure/timeout and cleanup; source/raw/sample tampering; CLI
smoke; and absence of implicit control or selected execution.

Complete-parity generation, SMT-LIB documentation parity, the known unrelated
link exception, and clean local/tracking/remote equality must pass. R6 stops on
any mismatch, consumes at most one selected process, never rewrites R5, and
does not adjust memory, stack, timeout, shard, command, or artifact semantics
after observation.
