# Lane: coordinator — working the curriculum DAG toward the autogenesis frontier

<!-- plan-section: lane-status -->

**Curriculum-directed kernel development (`WIP`, coordinator, 2026-08-25).**
Targets are chosen per
[doc 262](../../autogenesis/262-curriculum-directed-frontier-selection.md): the
curriculum DAG picks the subject, `fact-frontier.py` picks the row. The kernel
stands at **1,096 distinct theorems, every one axiom-free**, trusted base
unmoved at 30 declared-and-unreached `axreal` assumptions — and there are **no
`Opaque` and no `Quotient` declarations in any prelude builder**, measured, so
`Axiom`-only and the full trusted surface coincide everywhere today.

**The frontier selects.** It refused every candidate for the whole programme's
history — `no-registered-operation` on all 196 rows — because the registry was a
dispatch table: 26 operations, 24 naming exactly one fact, every one of them
already proved. One operation naming several open dependency-ready facts changed
that, and `execute-autogenesis-operation.py --dry-run-multi-target` now runs the
whole chain — selection, dispatch, independent re-derivation,
`would_admit=F:ml430-nat-modeq-symm-0a3d4d18` — **with no ledger write**. What
stands between that and an automatic admission is the authoritative receipt
schema, which is an ADR decision and was deliberately not invented.

**The ledger went 362 → 458 facts**, and the measurement that prompted it is
the number worth carrying: **1,018 of 1,053 admitted theorems (97%) had no
fact**, `rat` was 220-of-220 uncovered, and `complex`/`cpoint`/`logic` were at
zero. `theorem_dependency_inventory` was extended to the constructed carriers,
which had been outside its coverage entirely.

Detail and older landed rows moved to [`../notes/124-curriculum-frontier.md`](../notes/124-curriculum-frontier.md).

Detail and older landed rows moved to [`../notes/124-curriculum-frontier.md`](../notes/124-curriculum-frontier.md).

<!-- plan-section: landed-changes -->

| 2026-08-25 | `beb27f1ba` | **The trusted-core ceiling, raised the way the gate demanded.** Guard C failed at 5,508 past 5,500 with "say why before raising it." The baseline was RE-DERIVED by `git archive` rather than trusted, giving a per-file table summing to exactly +379 (`tc.rs` +347, `inductive.rs` +30, `env.rs` +2). Verdict: real and necessary — a universe-parameter closure fixing declarations **official Lean 4.30.0 refuses but this kernel wrongly admitted**, and `whnf_core` memoisation (138× cost, 1,857 s → 13.4 s) inside `def_eq`. Ceiling 5,900 with headroom matching the original's character; guard C re-verified to fire by injecting 500 lines in a scratch copy. The file's own comment said "5,110" where the real baseline was 5,129 — wrong from day one. |
