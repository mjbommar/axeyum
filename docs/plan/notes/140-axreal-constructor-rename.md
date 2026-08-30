# Notes: 140-axreal-constructor-rename

Detail moved out of [`../status/140-axreal-constructor-rename.md`](../status/140-axreal-constructor-rename.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Task 2 (provenance-ledger join).** The five `Int.ModEq` shift-family facts
closed by `authoritative-kernel-int-modeq-shift-family-v1` never carried
`evidence[].checker_operation.id`, so `gen-production-provenance-ledger.py`
credited the operation's generality but not the facts. Added one evidence row
per fact with `checker_operation: {"id": "authoritative-kernel-int-modeq-shift-family-v1"}` —
deliberately WITHOUT the sha256/manifest receipt fields every other
`checker_operation` row carries, since those come from
`execute-autogenesis-operation.py`'s `run_registered` dispatcher, which has no
case for this operation's `executor.driver`
(`axeyum-lean-kernel/authored-declaration-v1` — confirmed by reading the
dispatcher's final `raise ExecutionError`). Inventing matching hashes would
have fabricated provenance; the schema (`additionalProperties: true` on
evidence items) and the cross-check in `validate-autogenesis-operations.py`
(only requires `checker_operation.id` be a string naming the fact's own
operation) both permit the minimal shape.

**Measured.** `cargo check -p axeyum-solver --all-targets --features full`
clean; `cargo test -p axeyum-solver --lib --features full` (release) 1435
passed, 0 failed, 27.23s; `--test farkas_over_the_integers --features full`
9/9 (7.92s); `--test front_door_reaches_no_real_axiom --release --features
full` 1/1 (6.46s; debug SIGABRTs on the known deep-kernel-stack gotcha,
unrelated); `--test sos_lean_reconstruct --release --features full` 14/14
(6.20s). `validate-facts.py` 806 facts / 0 errors (unchanged, evidence-only
edit); `validate-autogenesis-operations.py` OK, operations=28;
`gen-production-provenance-ledger.py --check` clean, `facts_via_multi_target`
14 -> 19, `multi_target_operations` unchanged at 4;
`check-autogenesis-holdout-isolation.py` PASS.

**Environment note.** `/` filled to 0 bytes free mid-session (869 GB used of
915 GB) — a host-wide condition, not caused by this lane's changes; freed 5.7
GB by clearing this worktree's own `target/debug/{deps,incremental,build}`
(safe: single-lane worktree) to unblock `git commit`. Did not touch
`cargo check --workspace --all-features`, which additionally needs a
`z3-static`/`zstd-sys` C build the disk pressure was blocking when tried;
per-crate `--features full` checks above are what the task's verification
section actually asked for and are unaffected.
