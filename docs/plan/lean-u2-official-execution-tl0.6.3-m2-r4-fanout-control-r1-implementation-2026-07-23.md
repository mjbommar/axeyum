# Lean U2 TL0.6.3 M2 R4 fanout-control R1 implementation checkpoint

Status: **corrected, tested, committed, and pushed; corrected control and
selected attempt not run**

Date: 2026-07-23

Parent:
[R1 correction plan](lean-u2-official-execution-tl0.6.3-m2-r4-fanout-control-r1-plan-2026-07-23.md)

## Published correction

The correction plan was committed and pushed first as `2405741e`. The separate
implementation commit is `d8b0404bdb52d8d1a3d2085332ce46f3d19e9f77`.

| Corrected input | SHA-256 |
|---|---|
| `scripts/lean_u2_official_execution_m2_r4.py` | `7f425a24c69d0f234d750cc5b8fd9e5d08ab0d0ead0136f133d6168634016a55` |
| `scripts/tests/test_lean_u2_official_execution_m2_r4.py` | `a00401dd569296b1ca3cc01fd98199262bcb18c90a069c20d094255294b73435` |
| generated complete-parity report | `c6735fb0e2404956f0f8cce602a76409385d7fd3914f980ef63e7e055cd0a0ba` |

The implementation adds only the preregistered `do` token after the task-join
lambda binder. A focused source-shape assertion prevents recurrence. No memory,
stack, task count/priority, exact output, cleanup, selected command, shard,
timeout, evidence, or credit field changed.

## Validation and boundary

The five focused R4 tests, offline contract, complete-parity generator/check,
nine complete-parity tests, and SMT-LIB documentation parity check pass. The
complete-parity terminal remains false with zero complete populations, axes,
pairs, and gates. Validation did not execute released Lean.

The first failed fanout control and its diagnostic repetition remain no-credit
preflight observations. They created no selected source capture, harness,
discovery, prelaunch record, work root, or evidence root; attempt 003 is still
unconsumed. After this checkpoint is committed and pushed, the corrected stack
and fanout controls may run from that new clean remote-equal revision. A valid
fanout record digest is required before the one selected invocation.
