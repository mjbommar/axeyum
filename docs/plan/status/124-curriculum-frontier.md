# Lane: coordinator — working the curriculum DAG toward the autogenesis frontier

<!-- plan-section: lane-status -->

**Curriculum-directed kernel development (`WIP`, coordinator, 2026-08-25).**
Targets are chosen per
[doc 262](../../autogenesis/262-curriculum-directed-frontier-selection.md): the
curriculum DAG picks the subject, `fact-frontier.py` picks the row. The kernel
stands at **1,079 distinct theorems, every one axiom-free**, trusted base
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

<!-- plan-section: landed-changes -->

| 2026-08-25 | `978340925` | **ℚ is an ordered field, by composition.** `Rat.IsOrderedField := IsField ∧ (translation-invariance ∧ closure-of-the-nonnegatives)`, reusing `rat_isField` verbatim because its declared type is already the folded application. All three briefed consequences already existed and were verified rather than re-derived. Its negative control drops BOTH hypotheses from `mul_nonneg` and is over a genuinely false statement (`1·(-1) = -1`), not merely an under-justified one. |
| 2026-08-25 | `865bab083` | **No fact checker consumes a pipeline with `grep -q`, and a guard so none does again.** 81 facts / 132 commands rewritten to `test "$(… \| grep -c …)" -ge 1`, every non-`checker_command` field asserted byte-identical per file. The guard immediately caught 18 facts two other lanes added after its base. The defect is flakiness, not unsoundness — it fails closed — but it is real: `set -o pipefail; seq 200000 \| grep -q '^1$'` exits **141**. |
