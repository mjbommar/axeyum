# Lean U2 TL0.6.3 M2 R4 attempt-003 implementation checkpoint

Status: **implemented, tested, committed, and pushed; no released-Lean R4
control, selected harness, discovery, or process has run**

Date: 2026-07-23

Parent:
[R4 attempt-003 plan](lean-u2-official-execution-tl0.6.3-m2-r4-attempt-003-plan-2026-07-23.md)

## 1. Published implementation

The source-first plan is commit
`42b3e6b2ca7327763f3fd57fef70d0421f8950dc` with SHA-256
`b38566390250d98d3e4c1667c6a3a4215ac5ac962cdc96686b0c7fc6a2307d1e`.
The separately pushed implementation is commit
`3748427d17ca94d3ca477ac6b59584f4edd8be91`.

| Published input | SHA-256 |
|---|---|
| `scripts/lean_u2_official_execution_m2_r4.py` | `ff1f322ea8a01636330ef1a9a30fabc279bacb77685df80f2f6d39ae251bb771` |
| `scripts/tests/test_lean_u2_official_execution_m2_r4.py` | `8bdc8f7bb182438f9903dfb36320a3f67cf16e894b5e529735bacffb0b9525bc` |
| generated complete-parity report | `6df00ce74db103f629dbd04df9d788b54a0fe3b74bf280479103e541d71b147a` |

The new module validates R1/R2 through the frozen R3 validator, then validates
R3 authority record `e972d2ec...af1dbc`, terminal `c228a80e...6c6f6`, the
17-file / 4,908,035-byte incomplete store, and zero credits. It assigns run
`tl0.6.3-m2-release-linux-shard-0001-v3` / `attempt-003` / sequence 3 and
requires new revision-named work and evidence roots.

## 2. Single resource delta and controls

The R4 resource envelope differs from R3 only in lane identity and the frozen
address-space value: 8,589,934,592 becomes 17,179,869,184 bytes. The exact
64-case order, CTest `-j1` command, one-hour watchdog, released toolchain,
`LEAN_STACK_SIZE_KB=524288`, wrapper bytes, 124/67/56/1 artifact split, and
completion-last store remain unchanged.

The module adds two explicit, no-credit preflight surfaces:

- the existing direct environment probe must observe `524288` inside released
  Lean;
- a new UTF-8 source creates nine `Task.Priority.dedicated` tasks, joins every
  task through `IO.wait`/`IO.ofExcept`, requires the exact line
  `R4_FANOUT_OK|tasks=9|sum=36`, runs under 16 GiB `RLIMIT_AS`, and records its
  source bytes/hash, command, environment, terminal, peak direct-child RSS,
  and empty post-cleanup process group.

`run-r4` repeats and binds the fanout control before source capture or harness
construction. The caller must supply the record digest from a separate
explicit observation; mismatch stops before selected discovery. Neither
control has a selected case ID or any credit field.

## 3. Validation

- 5/5 focused R4 tests pass. They cover exact R1-R3 history, distinct roots,
  spec identity, one-variable resource comparison, wrapper byte equality,
  harmless control command/environment/limit/output/cleanup, a negative
  control, 16 GiB process classification with global restoration, the exact
  124/67/56/1 projection, mixed JUnit projection, zero terminal promotion,
  and CLI smoke with no implicit control or selected process.
- The 7 R3 tests and 9 complete-parity tests also pass, including the immutable
  timeout authority and generated-source identity integration.
- R3 offline and retained-incomplete validators, R4 offline validation, the
  complete-parity generator/check, and the SMT-LIB documentation parity check
  pass. The latter remains 992 files, 753 decisions, 680 comparisons, and zero
  recorded disagreement.
- The only link report is the pre-existing SMT-COMP README target
  `../checked-finite-profile-quantified-uf-models-2026-07-22.md`; this R4
  checkpoint adds no link failure.
- Generated terminal state remains zero complete populations, zero complete
  axes, zero paired cells, zero satisfied gates, and `terminal_ready=false`.

No released-Lean R4 control, selected harness, discovery, prelaunch record,
evidence root, or CTest process exists at this checkpoint.

## 4. Invocation boundary

After this checkpoint is pushed, the next action is an external read-only
preflight from its clean remote-equal revision. It must recheck all published
hashes and history, exact source/toolchain, absent R4 roots, then explicitly run
and retain both harmless controls. Only the resulting fanout record digest may
authorize `run-r4` once with the full same revision and exact
`/home/mjbommar/.cache/axeyum-tl063-m2-r4-<short-revision>` root. Once selected
discovery or CTest exists, attempt 003 is consumed. Any failure is retained
with zero credit and no retry.
