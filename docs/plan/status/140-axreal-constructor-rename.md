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

Detail moved to [`../notes/140-axreal-constructor-rename.md`](../notes/140-axreal-constructor-rename.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `6bdb1e35f` | ADR-0605 3: `LraReconstructCtx::new`/`::try_new` renamed to `new_over_axreal`/`try_new_over_axreal`, `Default` removed, every call site updated, `axreal_call_site_guard` added (3 tests, proved discriminating by hand). `cargo test -p axeyum-solver --lib --features full` 1435/0 failed; `farkas_over_the_integers` 9/9; `front_door_reaches_no_real_axiom`/`sos_lean_reconstruct` 1/1, 14/14 (release). |
| 2026-08-27 | `c86fadafe` | Five `Int.ModEq` shift-family facts joined to `authoritative-kernel-int-modeq-shift-family-v1` via a minimal `checker_operation.id` evidence row (no fabricated receipt fields — no executor case exists for this driver). `validate-facts.py` 806/0; ledger `facts_via_multi_target` 14 -> 19. |
