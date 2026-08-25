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

<!-- plan-section: landed-changes -->

| 2026-08-25 | `beb27f1ba` | **The trusted-core ceiling, raised the way the gate demanded.** Guard C failed at 5,508 past 5,500 with "say why before raising it." The baseline was RE-DERIVED by `git archive` rather than trusted, giving a per-file table summing to exactly +379 (`tc.rs` +347, `inductive.rs` +30, `env.rs` +2). Verdict: real and necessary — a universe-parameter closure fixing declarations **official Lean 4.30.0 refuses but this kernel wrongly admitted**, and `whnf_core` memoisation (138× cost, 1,857 s → 13.4 s) inside `def_eq`. Ceiling 5,900 with headroom matching the original's character; guard C re-verified to fire by injecting 500 lines in a scratch copy. The file's own comment said "5,110" where the real baseline was 5,129 — wrong from day one. |
| 2026-08-25 | `0cad43324` | **The derived-deps gate was blind to 331 theorems.** Its namespace alternation never included `CReal\|Complex\|CPoint`, so it enforced nothing over `creal`/`complex`/`cpoint`. Widening it exposed **279 missing `depends_on` edges across 33 facts**, all applied; the gate's own "not enforced" advisory list — which had been printing the blind spot all along — fell 135 → 80. Anchored with `(?<![A-Za-z])` plus a near-miss control, because `contains("Real.")` matches `CReal.` and has bitten twice. |
| 2026-08-25 | `83450f2ae` | **The loop is code-complete: selection → receipt → checkable transaction.** Reproduced end to end here, digest byte-identical to the lane's. It refuses what it must — a receipt relabelled to a sibling fact **and re-signed** is still rejected, because `--verify` re-derives every value from the live frontier and trusts the receipt only for its own digest. The fact stays `open` on purpose: the machinery being checkable is the milestone, and whether to WRITE is not a decision a gate should make. |
| 2026-08-25 | `a5f90e49b` | **68 fact checkers reported present theorems as ABSENT from any script.** `\t` in an ERE pattern is a literal `t` to GNU grep; this host's interactive `grep` is a function wrapping ugrep and reads a tab, so they passed by hand and failed everywhere else. A lane found it nested one level deeper — `[^\t]` inside a bracket expression means "not backslash and not t". All rewritten to `[[:space:]]`, gated. Also here: the chain rule, completing the standard differentiation rules. |
| 2026-08-25 | `c6e0176e1`, `e1d345e1e` | **Five curriculum nodes opened and the algebraic ladder completed.** `sets` 0→28 (with `Subset` as the kernel's first partial order), `groups` with ℤ/n, `rings` with ℤ and **ℤ/6 as the kernel-checked counterexample** that makes "integral domain" a distinction, `fields` with ℚ ordered by composition, and the **symmetric group** as a witnessed `IsGroupOnFn` — which required first REFUTING the predicate, unsatisfiable because it used unbounded function equality where `permInverse` inverts only on `[0,n)`. |


| 2026-08-25 | `978340925` | **ℚ is an ordered field, by composition.** `Rat.IsOrderedField := IsField ∧ (translation-invariance ∧ closure-of-the-nonnegatives)`, reusing `rat_isField` verbatim because its declared type is already the folded application. All three briefed consequences already existed and were verified rather than re-derived. Its negative control drops BOTH hypotheses from `mul_nonneg` and is over a genuinely false statement (`1·(-1) = -1`), not merely an under-justified one. |
| 2026-08-25 | `865bab083` | **No fact checker consumes a pipeline with `grep -q`, and a guard so none does again.** 81 facts / 132 commands rewritten to `test "$(… \| grep -c …)" -ge 1`, every non-`checker_command` field asserted byte-identical per file. The guard immediately caught 18 facts two other lanes added after its base. The defect is flakiness, not unsoundness — it fails closed — but it is real: `set -o pipefail; seq 200000 \| grep -q '^1$'` exits **141**. |
