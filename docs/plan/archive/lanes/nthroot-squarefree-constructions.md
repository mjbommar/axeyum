# Lane: nthroot-squarefree-constructions — declare `Nat.nthRoot`/`Squarefree` to unblock a future nursery draw

<!-- plan-section: lane-status -->

**Done (`DONE`, nthroot-squarefree-constructions, 2026-08-30).** Declared
`Nat.nthRoot`/`Nat.nthRootAux` (`nth_root.rs`) and `Squarefree`/
`Nat.squarefreeAux` (`squarefree.rs`) in the Nat prelude — construction and
evaluation test only, ADR-0653 discipline, no theorem about either. Full
detail and every re-derived number: ADR-0910.

Re-verified before building: ADR-0762's enumeration (either constant alone
gives 0 lawful family sets, both together give the two new held-out-safe
modules R5 needs) still holds on this tree, byte-identical to ADR-0830's own
re-measurement (env=2383, same un-owned floor modulo the four ADR-0830
already drew). The brief's cited "ADR-0900 (draw 10, declined)" does not
exist in this worktree or `origin/main` (ADR index tops out at 0855) — not
inherited, reported instead.

Re-screened after declaring: `Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas`
(13 rows) and `Mathlib.Data.Nat.Squarefree` (11 rows) both open, both R9
0/10 (neither module's first ten screened rows collides with a name this
kernel already declares). `nat_prelude::` sweep: 229 passed, 0 failed
(confirmed nonzero, includes both new evaluation tests plus the
environment-derived coverage assertion). `cargo clippy -p axeyum-lean-kernel
--lib -- -D warnings`: clean. Holdout isolation before/after: identical,
`held_out=136|files_scanned=1110|settled=0|references=0|verdict=PASS` —
`artifacts/autogenesis/` untouched (this lane enables a draw, does not
author one).

**What the next lane needs to know.** This does NOT regenerate
`artifacts/autogenesis/kernel-environment-snapshot-v1.json` (out of this
lane's scope) or run the real `select()`/`guard()` end to end — only the
`admissible()`/module-opening slice, in memory, confirming the prediction.
The next lane must: regenerate that snapshot from a fresh kernel build,
run the real draw, and read `docs/plan/notes/383-nursery-draw-8.md`'s two
`Nat.nthRoot`-specific warnings (the `nthRoot_zero_left`/`nthRoot_one_right`
closed-evaluation spend this construction's own equations create, and
whether `Nat.nthRoot.lt_pow_go_succ_aux` — a Mathlib-internal auxiliary
about ITS OWN Newton iteration, not ours — is a fair blind target) before
drawing either module.

<!-- plan-section: landed-changes -->

| 2026-08-30 | nthroot-squarefree-constructions | `Nat.nthRoot`/`Squarefree` declared (construction + evaluation test only); un-owned floor now opens both modules ADR-0762/ADR-0830 named, R9-clean; nothing under `artifacts/autogenesis/` touched |
