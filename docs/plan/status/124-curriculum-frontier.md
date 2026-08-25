# Lane: coordinator — working the curriculum DAG toward the autogenesis frontier

<!-- plan-section: lane-status -->

**Curriculum-directed kernel development (`WIP`, coordinator, 2026-08-25).**
Target selection follows
[doc 262](../../autogenesis/262-curriculum-directed-frontier-selection.md): the
curriculum DAG picks the subject, `fact-frontier.py` picks the row. Doc 262's
first amendment recorded 18 of 23 nodes as "solver-backed and kernel-empty";
**five of those are no longer empty** — `sets` 0→28, `groups` 0→4 (with ℤ/n as
a worked instance), `relations-and-functions` 0→5, `cardinality` 0→1,
`polynomials` 0→4 — and the second amendment records the measurement. The
kernel stands at **1,053+ distinct theorems, every one axiom-free**, trusted
base unmoved at 30 declared-and-unreached `axreal` assumptions.

The fact ledger went from **362 to 410 facts** across four lanes. The gap they
measured first is the number worth carrying: **1,018 of 1,053 admitted theorems
(97%) had no fact**, and `rat` was 220-of-220 uncovered — zero facts anywhere
named a theorem originating in the ℚ prelude. `theorem_dependency_inventory`
was extended to build `creal`/`complex`/`cpoint`, which had been outside its
coverage entirely, so a fact over those 423 theorems can now get a derived
`depends_on` instead of a hand-asserted one.

Detail and older landed rows moved to [`../notes/124-curriculum-frontier.md`](../notes/124-curriculum-frontier.md).

<!-- plan-section: landed-changes -->

| 2026-08-25 | `978340925` | **ℚ is an ordered field, by composition.** `Rat.IsOrderedField := IsField ∧ (translation-invariance ∧ closure-of-the-nonnegatives)`, reusing `rat_isField` verbatim because its declared type is already the folded application. All three briefed consequences already existed and were verified rather than re-derived. Its negative control drops BOTH hypotheses from `mul_nonneg` and is over a genuinely false statement (`1·(-1) = -1`), not merely an under-justified one. |
| 2026-08-25 | `865bab083` | **No fact checker consumes a pipeline with `grep -q`, and a guard so none does again.** 81 facts / 132 commands rewritten to `test "$(… \| grep -c …)" -ge 1`, every non-`checker_command` field asserted byte-identical per file. The guard immediately caught 18 facts two other lanes added after its base. The defect is flakiness, not unsoundness — it fails closed — but it is real: `set -o pipefail; seq 200000 \| grep -q '^1$'` exits **141**. |
