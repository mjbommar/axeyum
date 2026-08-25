# Notes: 124-curriculum-frontier

Detail moved out of [`../status/124-curriculum-frontier.md`](../status/124-curriculum-frontier.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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

## Archived landed-changes rows

| 2026-08-25 | `865bab083` | **48 facts for ℕ/ℤ/ℚ/ℝ, and the coverage measurement behind them.** 97% of admitted theorems had no fact; `rat` was 220-of-220 uncovered. `theorem_dependency_inventory` extended to `creal`/`complex`/`cpoint` (and now requires `--release`; a debug build overflows its stack). Checkers verified BOTH ways — real name exit 0, wrong name nonzero — and the `--include-constructed` flag shown to be load-bearing by failing without it. |
| 2026-08-25 | `865bab083` | **`Nat.permInverse` — an explicit inverse for a bijection on `[0,n)`,** with both inverse laws, plus `Nat.id`, `comp_assoc`, and `IsGroupOnFn` over a carrier of FUNCTIONS. Needed because `bijective_of_injective_on` proves an EXISTS and `Exists.rec` eliminates only into `Prop`. Renamed from `inverseIndex`, which `int_prelude/wilson.rs` already owned. |
| 2026-08-25 | `865bab083` | **`scripts/lane-merge-additive.py`** — refuses a both-sides conflict resolution whose hunk sides are delimiter-unbalanced, and can `splice` whole items out of the other branch's file instead. 18 controls; the one that matters reproduces the exact failure shape and asserts that keeping both sides really does leave the delimiters unbalanced. |
| 2026-08-25 | `28a4e9553` | **`Subset` is a partial order and joins the lattice** (`subset_refl`/`_trans`/`_antisymm` pointwise, `setDiff_eq_inter_compl` as a bare `Eq.refl`, `union_eq_right_of_subset`), on top of 13 pointwise Boolean-lattice laws. Nothing in this kernel named an ORDER before; `relation.rs` had only equivalences. |
| 2026-08-25 | `c6e0176e1` | **Finite groups over ℕ with ℤ/n as the worked instance,** and the ℚ `sumRange` sample-rate law — whose more useful half is negative: the closed form cannot reach `Cauchy`, because the per-term error sum is harmonic. The module doc now names the tractable route instead of the dead end. |
| 2026-08-25 | `fd3888e63` | **The decoupling lane landed: no artifact depends on a repository we do not own** (ADR-0553). I verified the new gate FIRES rather than trusting its zero — exit 1 both on an artifact path containing `..` and on the original `ROOT.parent / "math-education"` script pattern. |
| 2026-08-25 | `28a4e9553` | **Two correspondence-gate defects found by lanes USING the gate, not by the gate.** `CARRIERS["Nat"]` could never match `AxNat` (the `x` blocks the word-boundary erasure), so kernel-spelled transports failed closed and the gate steered authors toward prose-ℕ. And a `specialization` whose every `via` ref was `null` passed — an empty route dressed as prose. Both controlled, including the discrimination that null refs stay legitimate for rearrangement steps. |

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

## Archived landed-changes rows

| 2026-08-25 | `865bab083` | **48 facts for ℕ/ℤ/ℚ/ℝ, and the coverage measurement behind them.** 97% of admitted theorems had no fact; `rat` was 220-of-220 uncovered. `theorem_dependency_inventory` extended to `creal`/`complex`/`cpoint` (and now requires `--release`; a debug build overflows its stack). Checkers verified BOTH ways — real name exit 0, wrong name nonzero — and the `--include-constructed` flag shown to be load-bearing by failing without it. |
| 2026-08-25 | `865bab083` | **`Nat.permInverse` — an explicit inverse for a bijection on `[0,n)`,** with both inverse laws, plus `Nat.id`, `comp_assoc`, and `IsGroupOnFn` over a carrier of FUNCTIONS. Needed because `bijective_of_injective_on` proves an EXISTS and `Exists.rec` eliminates only into `Prop`. Renamed from `inverseIndex`, which `int_prelude/wilson.rs` already owned. |
| 2026-08-25 | `865bab083` | **`scripts/lane-merge-additive.py`** — refuses a both-sides conflict resolution whose hunk sides are delimiter-unbalanced, and can `splice` whole items out of the other branch's file instead. 18 controls; the one that matters reproduces the exact failure shape and asserts that keeping both sides really does leave the delimiters unbalanced. |
| 2026-08-25 | `28a4e9553` | **`Subset` is a partial order and joins the lattice** (`subset_refl`/`_trans`/`_antisymm` pointwise, `setDiff_eq_inter_compl` as a bare `Eq.refl`, `union_eq_right_of_subset`), on top of 13 pointwise Boolean-lattice laws. Nothing in this kernel named an ORDER before; `relation.rs` had only equivalences. |
| 2026-08-25 | `c6e0176e1` | **Finite groups over ℕ with ℤ/n as the worked instance,** and the ℚ `sumRange` sample-rate law — whose more useful half is negative: the closed form cannot reach `Cauchy`, because the per-term error sum is harmonic. The module doc now names the tractable route instead of the dead end. |
| 2026-08-25 | `fd3888e63` | **The decoupling lane landed: no artifact depends on a repository we do not own** (ADR-0553). I verified the new gate FIRES rather than trusting its zero — exit 1 both on an artifact path containing `..` and on the original `ROOT.parent / "math-education"` script pattern. |
| 2026-08-25 | `28a4e9553` | **Two correspondence-gate defects found by lanes USING the gate, not by the gate.** `CARRIERS["Nat"]` could never match `AxNat` (the `x` blocks the word-boundary erasure), so kernel-spelled transports failed closed and the gate steered authors toward prose-ℕ. And a `specialization` whose every `via` ref was `null` passed — an empty route dressed as prose. Both controlled, including the discrimination that null refs stay legitimate for rearrangement steps. |
