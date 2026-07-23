# Lean U2 TL0.6.3 M2 R3 attempt-002 implementation checkpoint

Status: **implemented, tested, committed, and pushed; no selected harness,
discovery, or process has run**

Date: 2026-07-23

Parent:
[R3 attempt-002 plan](lean-u2-official-execution-tl0.6.3-m2-r3-attempt-002-plan-2026-07-23.md)

## 1. Published implementation

The source-first plan is commit
`ec64a52370a38c7b127ffe66160ab9cedd7d2b5f` with SHA-256
`c2aea0d4ae6c6affeed5a7d865f6e466bbb795efaa17361d3e5349d3c04ce961`.
The separately pushed implementation is commit
`d47dacc65a7970702c84197c1b8b829c1e704c5c`.

| Published input | SHA-256 |
|---|---|
| `scripts/lean_u2_official_execution_m2_r3.py` | `7f65466ad7197918c574ed3c40f74c60cb3f867e67151f178663dbdd806c341f` |
| `scripts/tests/test_lean_u2_official_execution_m2_r3.py` | `8b02728ee34122ff04565ebd1fcb2517c3123a316f231e6d9d194e15d163c44b` |
| generated complete-parity report | `c8edaebbd2a19c22e95f55be0df98bd45b4b5fe3b4c8ed1890f9e55ec6bdb93d` |

The new module is isolated from the frozen R1/R2 modules. It validates the
exact R1 authority and R2 post/completion identities, assigns run
`tl0.6.3-m2-release-linux-shard-0001-v2` / `attempt-002` / sequence 2,
requires the new revision-named work root and evidence namespace, and checks
local/tracking/remote equality before selected execution.

## 2. Corrected execution and evidence contracts

The generated stage1 wrapper contains exactly one
`export LEAN_STACK_SIZE_KB=524288`, preserves `TEST_LEAN_ARGS=(-j1)`,
`TEST_LEANI_ARGS=(-j1)`, and `LEAN_NUM_THREADS=1`, and rejects missing,
duplicate, zero, nonnumeric, or changed stack values. A harmless released-Lean
program run from pushed commit `d47dacc6` observed `524288` from inside the
direct runtime:

```text
LEAN_U2_M2_R3_STACK_PROBE|source=e7f746b0e0ded20ee76375877853dad4fdcaf32152168d0f0ca22a29e2a12401|exit=0|value=524288|selected_case=false
```

This control is not a selected U2 case and created no harness, discovery,
official outcome, or attempt credit.

Post-run closure now requires the exact family-aware 124-path structure:
64 `.out.produced` captures and three CTest logs are retained by bytes; 56
generated C/executable intermediates are retained as path/mode/byte/hash
metadata only; the wrapper is retained once as a harness artifact. All hashes
and byte totals are derived fresh. Completion is installed last and conflicts
never overwrite an existing record.

## 3. Validation

- 6/6 R3 tests pass, covering immutable history, new identities/root rules,
  wrapper mutations, the direct-runtime probe, exact registrations, the
  124/67/56/1 split, mixed 30-pass/34-fail projection, synthetic process
  eligibility, completion conflict handling, CLI smoke, and zero implicit
  selected execution.
- 31/31 combined M2/R1/R2/R3 tests pass; every offline CLI passes.
- 264 Lean-focused tests pass with one intentional skip through the direct
  `unittest` fallback (`just` is not installed on this host).
- The complete-parity generator/check and SMT-LIB documentation parity check
  pass: 992 files, 753 decisions, 680 comparisons, zero recorded disagreement.
- Generated terminal state remains zero complete populations, zero complete
  axes, zero paired cells, zero satisfied gates, and `terminal_ready=false`.

No selected R3 harness, discovery, prelaunch record, evidence root, or CTest
process exists at this checkpoint.

## 4. Invocation boundary

The next action is an external read-only preflight from a clean pushed head:
recheck plan/module/test hashes, R1/R2 closure, exact source/toolchain, absent
new roots, local/tracking/remote equality, and the harmless stack probe. Only
then may `run-r3` be invoked once with the full current revision and the exact
`/home/mjbommar/.cache/axeyum-tl063-m2-r3-<short-revision>` work root. Once
selected discovery or CTest exists, attempt 002 is consumed. Any failure is
retained with zero credit and no retry.
