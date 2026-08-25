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

**Next.** (1) Coverage is 111 of ~1,100 theorems; the largest holes are Nat by
absolute count and CReal by fraction. (2) Both curriculum **destinations** are
still kernel-thin and, more importantly, still carry **zero nursery pressure** —
doc 262's Gap 2, unchanged, and the sharper of the two. (3) The multi-target
receipt schema needs an ADR. (4) `just check` has six recipes red for
pre-existing reasons, under repair.

**Three findings outrank the counts.**

*The binding constraint is a missing TYPE.* No `List`, no `Finset`, no product.
It is why `det2` takes four scalars, why a permutation cannot be a group
element, and why `polyEval_mul` cannot be stated without vanishing hypotheses.
Every instance was found by a lane trying to prove the theorem, never by
planning.

*Two targets I named were FALSE, and lanes refuted them rather than failing.*
The ℚ Cauchy product does not hold for arbitrary coefficients — `conv` sums the
full antidiagonal, including points outside the `m×n` rectangle — shown with a
kernel-confirmed counterexample. And `Nat.IsGroupOnFn` is **unsatisfiable at the
symmetric group**: its conjuncts use unbounded `Eq (Nat → Nat)` while
`permInverse` inverts only on `[0,n)`. A node's frontier is characterised as
much by what is false there as by what is proved.

*Five checkers could not fail, and one guarded the headline claim.*
`prelude_axiom_inventory` parsed no arguments and always exited 0, and because
it built 3 of 9 preludes the axiom ledger's cross-check was satisfied
**vacuously for the other six**. `nat_axiom_inventory` gave a real prelude and a
typo the same message. `theorem_dependency_inventory` SIGABRTed behind a vacuity
guard, hiding 21 real missing `depends_on` edges. 81 facts consumed a pipeline
with `grep -q`. And 15 control suites ran nowhere at all — including
`test_validate_facts`, which guards the fact ledger itself.

<!-- plan-section: landed-changes -->

| 2026-08-25 | `978340925` | **ℚ is an ordered field, by composition.** `Rat.IsOrderedField := IsField ∧ (translation-invariance ∧ closure-of-the-nonnegatives)`, reusing `rat_isField` verbatim because its declared type is already the folded application. All three briefed consequences already existed and were verified rather than re-derived. Its negative control drops BOTH hypotheses from `mul_nonneg` and is over a genuinely false statement (`1·(-1) = -1`), not merely an under-justified one. |
| 2026-08-25 | `865bab083` | **No fact checker consumes a pipeline with `grep -q`, and a guard so none does again.** 81 facts / 132 commands rewritten to `test "$(… \| grep -c …)" -ge 1`, every non-`checker_command` field asserted byte-identical per file. The guard immediately caught 18 facts two other lanes added after its base. The defect is flakiness, not unsoundness — it fails closed — but it is real: `set -o pipefail; seq 200000 \| grep -q '^1$'` exits **141**. |
| 2026-08-25 | `865bab083` | **48 facts for ℕ/ℤ/ℚ/ℝ, and the coverage measurement behind them.** 97% of admitted theorems had no fact; `rat` was 220-of-220 uncovered. `theorem_dependency_inventory` extended to `creal`/`complex`/`cpoint` (and now requires `--release`; a debug build overflows its stack). Checkers verified BOTH ways — real name exit 0, wrong name nonzero — and the `--include-constructed` flag shown to be load-bearing by failing without it. |
| 2026-08-25 | `865bab083` | **`Nat.permInverse` — an explicit inverse for a bijection on `[0,n)`,** with both inverse laws, plus `Nat.id`, `comp_assoc`, and `IsGroupOnFn` over a carrier of FUNCTIONS. Needed because `bijective_of_injective_on` proves an EXISTS and `Exists.rec` eliminates only into `Prop`. Renamed from `inverseIndex`, which `int_prelude/wilson.rs` already owned. |
| 2026-08-25 | `865bab083` | **`scripts/lane-merge-additive.py`** — refuses a both-sides conflict resolution whose hunk sides are delimiter-unbalanced, and can `splice` whole items out of the other branch's file instead. 18 controls; the one that matters reproduces the exact failure shape and asserts that keeping both sides really does leave the delimiters unbalanced. |
| 2026-08-25 | `28a4e9553` | **`Subset` is a partial order and joins the lattice** (`subset_refl`/`_trans`/`_antisymm` pointwise, `setDiff_eq_inter_compl` as a bare `Eq.refl`, `union_eq_right_of_subset`), on top of 13 pointwise Boolean-lattice laws. Nothing in this kernel named an ORDER before; `relation.rs` had only equivalences. |
| 2026-08-25 | `c6e0176e1` | **Finite groups over ℕ with ℤ/n as the worked instance,** and the ℚ `sumRange` sample-rate law — whose more useful half is negative: the closed form cannot reach `Cauchy`, because the per-term error sum is harmonic. The module doc now names the tractable route instead of the dead end. |
| 2026-08-25 | `fd3888e63` | **The decoupling lane landed: no artifact depends on a repository we do not own** (ADR-0553). I verified the new gate FIRES rather than trusting its zero — exit 1 both on an artifact path containing `..` and on the original `ROOT.parent / "math-education"` script pattern. |
| 2026-08-25 | `28a4e9553` | **Two correspondence-gate defects found by lanes USING the gate, not by the gate.** `CARRIERS["Nat"]` could never match `AxNat` (the `x` blocks the word-boundary erasure), so kernel-spelled transports failed closed and the gate steered authors toward prose-ℕ. And a `specialization` whose every `via` ref was `null` passed — an empty route dressed as prose. Both controlled, including the discrimination that null refs stay legitimate for rearrangement steps. |
