# Lean U2 TL0.6.3 M2 R2 diagnostic-closure result

Status: **append-only diagnostic closure complete; zero processes and zero outcome/parity credit added**

Date: 2026-07-22

The pushed [R2 plan](lean-u2-official-execution-tl0.6.3-m2-r2-diagnostic-closure-plan-2026-07-22.md)
and [implementation checkpoint](lean-u2-official-execution-tl0.6.3-m2-r2-diagnostic-closure-implementation-2026-07-22.md)
authorized one zero-process append. From clean, remote-equal revision
`beaa171b80be6adb5c3d450d47da2cfc54c0f6df`, `append-diagnostic` revalidated
the exact 83-file R1 root, unchanged original source, and frozen 124/67/56/1
work projection, then installed completion last.

| Result | Value |
|---|---|
| new processes / outcomes | 0 / 0 |
| retained payloads | 67 / 106,610 bytes |
| manifest-only intermediates | 56 / 950,219,754 bytes |
| new diagnostic namespace | 69 files / 159,346 bytes |
| diagnostic manifest | `19120b7bc959d3624d9db3bbfdcb54f8534899a7eed749063b39aafbaeb8abad` under `axeyum-lean-u2-official-execution-m2-r2-diagnostic-evidence-v1` |
| whole evidence root | 152 files / 5,307,372 bytes |
| whole-root manifest | `367a3d66e1f2d8d5a282df9e679faaea3315a743f95cee611b6740d5f2fd9462` under `axeyum-lean-u2-official-execution-m2-r2-whole-evidence-v1` |
| diagnostic completion record | `5ef1040a692a7a72650868909f7477beddf770093e86e2162bec5ff3745d459b` |

Post-append `offline-check` succeeds. All original R1 bytes remain unchanged;
the original `post.json`, `projection.json`, and `completion.json` remain
absent. R1 is still `invalid-post-artifact-closure`, its 64 JUnit rows remain
diagnostic, and shard/outcome credit remains zero.

This result establishes the sustainable future evidence policy but does not
authorize a retry. A later source-first attempt must use a new attempt/root,
freeze universal `LEAN_STACK_SIZE_KB` control for direct docparse and generated
executables, and preserve the family-specific retained-byte policy before any
process runs. The subsequently preregistered
[R3 attempt-002 plan](lean-u2-official-execution-tl0.6.3-m2-r3-attempt-002-plan-2026-07-23.md)
does exactly that: it preserves this result as immutable history, assigns new
run/work/evidence identities, freezes `LEAN_STACK_SIZE_KB=524288`, and permits
at most one new process only after separately pushed implementation gates.
