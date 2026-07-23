# Lean U2 TL0.6.3 M2 R5 attempt-003 implementation checkpoint

Status: **implemented, tested, committed, and pushed; no released-Lean R5
control, harness, discovery, or selected process has run**

Date: 2026-07-23

Parent:
[R5 attempt-003 plan](lean-u2-official-execution-tl0.6.3-m2-r5-attempt-003-plan-2026-07-23.md)

## Published implementation

The source-first plan is pushed commit
`107ee5522e3a29bc70258c82d75aa12601a1082f`, with plan SHA-256
`12fc9fc218f31a105b09634da875ccebd653bcb92bde96ad605cc057297d6b82`.
The separate implementation is pushed commit
`1d1c8ab8bcd379696f778004eed87008d16e87cc`.

| Published input | SHA-256 |
|---|---|
| `scripts/lean_u2_official_execution_m2_r5.py` | `5dca1de2b0f5d64be0884b8a39e0c53dc746697a535f06c8597187d106ed2c93` |
| `scripts/tests/test_lean_u2_official_execution_m2_r5.py` | `2fc563be5ff494065004bf9182ecd5f74a5e430f63a273f8784a5176f00d27e0` |
| generated complete-parity report | `0c17d15502cdc05219893d4b00eaf51b33b9f0cb59262f62f4fbe9de7f76ac0b` |

R5 binds the exact R1-R4 history and absence of R4 selected roots. It reuses
selected `attempt-003` / sequence 3, assigns run v4 and new control/work/evidence
roots, and changes only lane identity and `RLIMIT_AS` from 16 to 32 GiB.

## Completion-grade control store

The explicit `run-control` surface validates a clean remote-equal full revision
and exact released Lean before creating the revision-named external root. It
installs source, host, spec, and prelaunch before launch; enforces 32 GiB with a
new session; samples direct-process `VmPeak`, `VmSize`, `VmRSS`, and threads;
classifies exit/signal/timeout; reaps the group; retains raw stdout/stderr and a
sealed terminal; and installs completion last over the exact eight-file
namespace.

Success and failure both produce completion-grade, zero-credit evidence. Only
exit 0, exact `R4_FANOUT_OK|tasks=9|sum=36`, empty stderr, a reaped child, and
zero live group members set `authorized_selected_execution=true`. `run-r5`
requires that completion and its explicit digest before it can construct a
selected harness. The exact source bytes, stack, shard, command, one-hour
selected watchdog, 124/67/56/1 tiered store, and terminal credit zeros remain
unchanged.

## Validation and invocation boundary

- 5/5 focused R5 tests pass, covering exact history/root absence, spec and
  one-variable resource identity, source byte equality, complete success and
  thread-failure control stores, raw tampering, authorization rejection, zero
  selected-attempt/credit fields, process samples, 32 GiB adapter behavior,
  global restoration, and CLI no-implicit-execution smoke.
- The five R4 tests and nine complete-parity tests pass; R5 is wired into both
  CI workflows, `just parity-docs`, and generated source identities.
- Offline R5, complete-parity generator/check, and SMT-LIB documentation parity
  checks pass. Terminal state remains zero complete populations/axes/pairs/
  gates and false readiness.
- The only link report remains the unrelated SMT-COMP README target.

No released-Lean R5 control, selected work/evidence root, harness, discovery,
prelaunch record, or selected process exists. After this documentation
checkpoint is pushed, one explicit stack probe and one `run-control` may run
from the new clean remote-equal revision. A failed completed control stops R5
without consuming attempt 003. A successful completion digest permits exactly
one `run-r5` invocation from the same revision and roots frozen by the plan.
