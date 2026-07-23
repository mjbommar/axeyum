# Lean U2 TL0.6.3 M2 R6 attempt-004 implementation checkpoint

Status: **implemented, tested, committed, and pushed; no R6 control, harness,
discovery, or selected process has run**

Date: 2026-07-23

Parent:
[R6 attempt-004 plan](lean-u2-official-execution-tl0.6.3-m2-r6-attempt-004-plan-2026-07-23.md).

## Published implementation

The source-first plan is pushed commit
`055a3d7fd17faa26de8d04ba896c70c5640f95c8`, with plan SHA-256
`80d6f4875dcd11a90c79940f4b460bd3ede25f67139f22565f79dd64d8b33754`.
The separate implementation is pushed commit
`ff2406b1b081306891d7e5e08b453bdf28506c67`.

| Published input | SHA-256 |
|---|---|
| `scripts/lean_u2_official_execution_m2_r6.py` | `27b0e5af6480d89c469283b530decb1053897496cfe059fe902a954c1a40d878` |
| `scripts/tests/test_lean_u2_official_execution_m2_r6.py` | `85c03e0ee6b5f5521d80d002ae669b433966e9b9851d65578d3a901a75b427d7` |
| generated complete-parity report | `4a32cb76b5b794036d289475a544872e9b9522e9154dd756efd21776ca5938eb` |

## Implemented delta

R6 validates R5's exact invalid diagnostic completion, creates attempt 004 /
sequence 4 and run v5 with fresh roots, and preserves the 32 GiB limit,
512 MiB Lean stack, selected shard/order/command, one worker, one-hour watchdog,
and completion-last store. Its fresh control delegates to the already-tested
completion-grade R5 mechanism under R6 plan, attempt, schema, root, and revision
bindings; selected execution still requires the explicit new completion digest.

The post builder validates JUnit before choosing generated paths. Zero failures
require 123 rows and 66 retained payloads; one or more failures require
`LastTestsFailed.log`, 124 rows, and 67 retained payloads. Both retain 56
metadata-only rows and one existing wrapper. The sealed post records the
predicate and selected branch; projection and completion reconstruct the same
count and reject an inverted, added, missing, reordered, or resealed mutation.

## Validation and invocation boundary

- 9/9 focused R6 tests pass: exact R5 closure/history, spec/attempt freshness,
  both conditional branches, both inverted-log mutations, resealed predicate
  mutation, control identity/credit, captured preflight delegation without
  recursion, binding restoration, and CLI no-implicit-execution smoke.
- The inherited five R5 control tests remain green for completion-grade success,
  failure, tamper, authorization, process limits, and cleanup behavior.
- R5, R5 diagnostic, R6, and complete-parity suites pass 27 aggregate cases.
  Generator/check and offline R6 pass with 0/10 complete populations, 0/12
  complete axes, zero pairs/gates, and `terminal_ready=false`.
- `ruff` and `black` are not installed locally; byte compilation, line-length,
  diff-whitespace, and the repository's direct Python gates are clean. The only
  link report remains the unrelated SMT-COMP README target.

No released-Lean R6 control, selected work/evidence root, harness, discovery,
prelaunch, or selected process exists. After this checkpoint is pushed and
clean local/tracking/remote equality is revalidated, run one direct stack probe
and one fresh completion-grade control. Only its exact successful completion
may authorize one `run-r6` invocation; failure stops before consuming attempt
004.
