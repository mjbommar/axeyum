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

**Next.** (1) `complex`/`cpoint` remain at zero facts — the tooling blocker is
gone, the rows are not written. (2) Both curriculum **destinations** are still
kernel-thin and, more importantly, still carry **zero nursery pressure**; doc
262's Gap 2 is the sharper one and is unchanged, because a producer cannot be
evaluated against a population containing nothing from its subject.
(3) `Rat.polyEval_mul` is open with its obstruction now characterised rather
than unknown. (4) Series convergence needs `sumRange_tail_le`'s `le` bound
converted to `Cauchy` shape.

**Two findings from working the nodes outrank the counts.** The binding
constraint is a **missing type** — no `List`, no `Finset`, no product — which is
why a permutation cannot be a group element, why `det2` takes four scalars, and
why Lagrange's identity at general `n` is unstatable. Each instance was found by
a lane trying to prove the theorem, never by planning. And **a brief can name a
false target**: `polyEval_mul` as I stated it is false for arbitrary
coefficients, and the lane refuted it with a kernel-confirmed counterexample
rather than failing to prove it. A node's frontier is characterised as much by
what is false there as by what is proved.

**Two process defects, both fixed rather than noted.** A prelude can declare
into another prelude's namespace, so a lane reading all of `nat_prelude/` could
not see that `int_prelude/wilson.rs` already owned `Nat.inverseIndex`; the nat
prelude built fine alone with the collision present and it surfaced 230 failures
downstream as `DeclarationExists { name: NameId(457) }`. And two lanes adding
functions to one file produce a conflict where keeping both sides does not
parse — `scripts/lane-merge-additive.py` now refuses that resolution and can
reconstruct instead.

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
