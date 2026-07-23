# Lean U2 TL0.6.3 M2 R6 completion-replay R2 implementation checkpoint

Status: **implemented, tested, committed, and pushed; qualifying replay not yet
performed from this checkpoint**

Date: 2026-07-23

Parent:
[R2 correction plan](lean-u2-official-execution-tl0.6.3-m2-r6-completion-replay-r2-plan-2026-07-23.md).

## Published implementation

The frozen evidence and source-first plan are pushed commit
`74b593aa3020be6d0d60df47696a1417dfa37fdc`, with plan SHA-256
`7455f7d48982c1da1360061043f9a6377b9ba1c860aee1707aa3c96d29143565`.
The separate validator correction is pushed commit
`ce319a9d1867df111736363294f2e109cc4dd19c`.

| Published input | SHA-256 |
|---|---|
| `scripts/lean_u2_official_execution_m2_r6.py` | `ec3a1a09996293ea68f40caf1b22c054f1888f67b97e50fb03b8da17f1a1dcfa` |
| `scripts/tests/test_lean_u2_official_execution_m2_r6.py` | `e4b0d8b1c0bae0d580475be90859231e01402a510ed41fd6aaa48f880fd80621` |
| generated complete-parity report | `5b2a690d844eb03e796085393f2ad92fd75c086d65684f079dd14154eee1eb6a` |

`build_completion(root, allow_completion=false)` preserves pre-install
rejection. `validate_complete_store` alone requests `true`, and accepted
inventory still excludes `completion.json`; therefore replay must reconstruct
the already-installed bytes rather than reseal a new dependency set.

Eleven focused R6 tests pass. The added test copies the exact committed root,
normalizes live read-only modes, proves default construction rejects completion,
proves explicit replay returns the existing completion, and proves portable
inventory is byte-identical before/after. No process or evidence write occurs.

After this checkpoint is pushed and local/tracking/remote equality is clean,
run the read-only `validate` command once against the frozen root. Only that
post-publication replay may support the accepted result; a mismatch leaves R6
zero-credit and cannot authorize a selected retry.
