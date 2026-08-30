# Lane: totient-even — two mirrors closed, `Nat.totient_even` hand-traced

<!-- plan-section: lane-status -->

**DONE for this dispatch (`totient-even`, 2026-08-29).**

**The task.** Land the two cheap totient mirrors the `totient-counting` lane
left a verified route for, then spend remaining budget on `Nat.totient_even`
(piece 2 of the `nat-totient` triage) — either build it, or produce a
hand-traced, numerically checked plan if a build is not safe to land in the
remaining budget.

## Part 1 — the two mirrors, closed

**`F:ml430-nat-dvd-two-of-totient-le-one-3642bf31`** and
**`F:ml430-nat-totient-eq-one-iff-68d883a0`** are both `proved`,
`proof_route: kernel-lean`, `axiom_footprint: []`. Verified the previous
lane's recorded route by BUILDING it rather than trusting it, and it held
with no case-split-order surprises:

- `Nat.dvd_two_of_totient_le_one` (`0 < a -> totient a <= 1 -> a | 2`):
  `trichotomy` at `c = 2` on `a`. `a < 2` combined with `0 < a` forces
  `a = 1` (`le_of_succ_le_succ` + `le_antisymm`), closed by a concrete `dvd
  1 2` witness (`one_mul` gives `2 = 1*2`). `a = 2` is `dvd_refl`. `2 < a`
  is refuted by the shared core below.
- `Nat.totient_eq_one_iff` (`totient n = 1 <-> n = 1 \/ n = 2`): reverse
  direction is two `def_eq` reductions (`totient 1 = totient 2 = 1`,
  `d.refl` accepted up to defeq). Forward direction shares the same
  `trichotomy` shape: `n < 2` splits again (`lt_or_eq_of_le`) into `n = 0`
  (contradicts `totient n = 1` via `totient 0 = 0` by defeq, refuted by
  `succ_ne_zero`) or `n = 1` (`or_inl`); `n = 2` is `or_inr`; `2 < n` uses
  the same shared refutation.
- Shared core, `totient_le_one_contradiction_above_two` (new,
  `totient_lemmas.rs`): from `Lt two x` and `Le (totient x) one`, derive
  `False` by composing `countRange_ge_two_of_two_witnesses` at witnesses
  `1` (`coprime_one_left_iff`, unconditional) and `pred x`
  (`coprime_succ_self`, after `x = succ (pred x)` via `succ_pred_of_pos`),
  then chaining the resulting `Le two (totient x)` against the hypothesis
  via `le_trans` into the impossible `Le two one`, refuted by peeling two
  `succ`s down to `not_succ_le_zero`.
- New local helper `trichotomy_elim`: a full three-way eliminator for
  `finite::trichotomy` (`Or (Lt x c) (Or (Eq x c) (Lt c x))` directly into a
  proof of one target), generalizing `finite.rs`'s `two_way_split` (which
  only eliminates the middle case). Also `dvd_intro`, a local copy of
  `divisibility.rs`'s private helper of the same name (this file's own
  local-copies-per-file convention).

Detail moved to [`../notes/295-totient-even.md`](../notes/295-totient-even.md).

