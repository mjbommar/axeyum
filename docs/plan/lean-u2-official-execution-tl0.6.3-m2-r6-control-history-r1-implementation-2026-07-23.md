# Lean U2 TL0.6.3 M2 R6 control-history R1 implementation checkpoint

Status: **implemented, tested, committed, and pushed; corrected control not yet
repeated; no selected process exists**

Date: 2026-07-23

Parent:
[R1 correction plan](lean-u2-official-execution-tl0.6.3-m2-r6-control-history-r1-plan-2026-07-23.md).

## Published correction

The source-first correction plan is pushed commit
`8bb97f77828706382bad8ee933fe76179c00dca2`, with SHA-256
`d5069a7cdcc139e18508f2db23b00b371866283a3b25d0bb8816e4642f999bde`.
The separate implementation is pushed commit
`70268f2d73604278604e1a8a247c090a1e5bb3cc`.

| Published input | SHA-256 |
|---|---|
| `scripts/lean_u2_official_execution_m2_r6.py` | `18af039b262f21fe3dba6ce161fb21e308c9390920102cb9c1b48bc0fc742716` |
| `scripts/tests/test_lean_u2_official_execution_m2_r6.py` | `90b739a89e0395b2be730b735e43b04bb11d45d78f77c5910960a6859c9a0a57` |
| generated complete-parity report | `17dd6cfee6672a77e8c640194c0c40d2805ca3b6970aee0128e825e1248b214c` |

R6 now captures the complete original R5 control-binding set at module load.
Its history validator snapshots the caller's current values, exposes the
captured originals while the R5 diagnostic closure validates, and restores the
caller values in `finally`. This covers plan/run/attempt/lane/control schemas
and both history/revision gates, not merely the recursive function pointer.

Ten focused R6 tests pass. The added regression enters the exact temporary R6
control binding, invokes rebound `R5.validate_history`, observes frozen R5
completion `2d5d43a7...`, proves the captured original history gate ran, and
proves the R6 caller binding plus outer R5 state were restored. Offline R6 and
complete-parity generation remain zero-process and terminal-false.

No corrected control root, selected work/evidence root, harness, discovery, or
selected process exists. After this checkpoint is pushed and remote equality is
revalidated, repeat the stack probe and run one fresh revision-named control.
Only its exact successful completion authorizes attempt 004 once.
