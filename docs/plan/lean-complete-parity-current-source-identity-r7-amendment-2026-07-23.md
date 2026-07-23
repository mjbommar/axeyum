# Lean complete-parity current-source identity R7 amendment

Date: 2026-07-23

Status: **preregistered scope correction before store-validator change; no
process, outcome, or parity credit authorized**

Parent:
[R7 current-source identity plan](lean-complete-parity-current-source-identity-r7-plan-2026-07-23.md)

Implementation checkpoint before amendment: `e7db3f69`

## 1. Newly exposed layer

The parent plan correctly separated the historical and current
`resume_fs.py` identities in the store test, TL0.7.4 acceptance validator, and
TL0.6.3 U2 validator. After that bounded implementation was committed, 93
focused tests passed with one expected live sentinel skip.

The first complete-parity replay then advanced beyond the original test and
failed while rebuilding the retained TL0.7.3 store authority:

```text
worktree--dependency--before-temp-open: kill cell source identity drift
```

`validate_process_evidence` compares every retained cell's recorded
`primitive_sha256` directly to the current checkout's bytes. The retained
cells correctly record historical SHA-256 `1968e7b6...`; current
`resume_fs.py` correctly hashes to reviewed successor `b05c3218...`.
Therefore the parent plan's read-only restriction on
`scripts/lean_execution_store.py` is too narrow to restore deterministic
historical replay.

This discovery changes no evidence fact. It reveals an additional validator
boundary that the initial single-test failure did not exercise.

## 2. Corrected authorized scope

R7 may now edit `scripts/lean_execution_store.py` and its test in exactly one
way:

1. result construction must select and validate the implementation revision's
   source-input rows before validating retained cells;
2. retained process evidence must compare `worker_sha256` and
   `primitive_sha256` to the selected result-source identities;
3. the accepted historical implementation revision must therefore use the
   immutable historical worker/primitive hashes already recorded in
   `HISTORICAL_RESULT_SOURCE_INPUTS`;
4. any newly generated result must still prove its implementation revision is
   an ancestor of `HEAD`, prove that revision contains the current source
   bytes, and validate its cells against those exact current worker/primitive
   hashes; and
5. direct synthetic-fixture validation continues to default to current source
   bytes.

No caller may supply an arbitrary unvalidated source hash to make a result
pass. The expected historical/current hashes must be derived only from the
already validated `result_source_inputs` selection.

Because changing the store validator changes a current repository input, R7
may also refresh only the exact current store-validator hashes in TL0.7.4,
TL0.6.3, and M2, followed by the exact current TL0.6.3 hash in M2. Their
historical rows stay unchanged.

## 3. Additional required controls

In addition to every parent-plan gate:

- all 16 retained TL0.7.3 cells must reproduce against historical
  worker/primitive identities;
- the live temporary 16-cell matrix must reproduce against the newly committed
  current worker/primitive identities;
- mutation of either selected expected hash must reject with source-identity
  drift;
- the committed TL0.7.3 authority, summaries, and 65-file evidence root must
  remain byte-identical; and
- an unknown, non-ancestor, or source-mismatched implementation revision must
  continue to reject before result construction.

The amendment still authorizes no Lean, Axeyum, M2.1--M2.7, solver, network,
installer, exporter, retained-evidence, or toolchain process. The temporary
synthetic store matrix remains the only process-bearing test allowed.

## 4. Nonclaims

This is an offline historical/current validator correction. It does not alter
SMT-COMP's recovery semantics, reconstruct evidence, widen a Lean feature,
complete a U2 population or axis, satisfy a terminal gate, or add parity
credit.
