# Lane: axreal-rename — the axiom-bearing constructor is no longer the obvious one

<!-- plan-section: lane-status -->

**ADR-0605 3 landed (`WIP`, axreal-rename, 2026-08-27).**
`LraReconstructCtx::new`/`::try_new` built the `AxReal` package (30 axioms,
this repository's entire remaining trusted surface) under the one name a
caller would reach for by default, with `Default` delegating to it. Renamed
to `new_over_axreal`/`try_new_over_axreal`, matching the existing
`try_new_over_integers`/`try_new_over_constructed_reals` convention, and
**removed `Default` entirely** rather than repointing it at a constructed
carrier — a silently-changed default is its own hazard, and every caller now
names its carrier explicitly. There is no more no-argument "convenience"
constructor at all.

Added a complementary guard, `reconstruct::arithmetic::axreal_call_site_guard`
— a rename alone does not stop a *future* call site from picking the
axiom-bearing constructor again. It scans `src/reconstruct/` from disk (not a
hand-maintained list) for the two AxReal constructor names outside any
`#[cfg(test)]` span. Three tests: a positive control (planted call outside
any test module IS flagged), a negative control (the same call inside
`#[cfg(test)] mod tests { ... }` is NOT flagged), and the real gate over the
actual tree. Proved discriminating by hand: temporarily reintroducing the
call at a shipped site turned exactly the gate test red and no other, then
reverted.

`axreal` itself is untouched — ADR-0605 retains it deliberately as the
negative control and as the instantiation proving the ordered-ring interface
generalization is genuine.

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

<!-- plan-section: landed-changes -->

| 2026-08-27 | `6bdb1e35f` | ADR-0605 3: `LraReconstructCtx::new`/`::try_new` renamed to `new_over_axreal`/`try_new_over_axreal`, `Default` removed, every call site updated, `axreal_call_site_guard` added (3 tests, proved discriminating by hand). `cargo test -p axeyum-solver --lib --features full` 1435/0 failed; `farkas_over_the_integers` 9/9; `front_door_reaches_no_real_axiom`/`sos_lean_reconstruct` 1/1, 14/14 (release). |
| 2026-08-27 | `c86fadafe` | Five `Int.ModEq` shift-family facts joined to `authoritative-kernel-int-modeq-shift-family-v1` via a minimal `checker_operation.id` evidence row (no fabricated receipt fields — no executor case exists for this driver). `validate-facts.py` 806/0; ledger `facts_via_multi_target` 14 -> 19. |
