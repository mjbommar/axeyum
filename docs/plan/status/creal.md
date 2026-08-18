# Lane: agent-creal-laws — ℝ constructed, and the ordered-ring laws over it

<!-- plan-section: lane-status -->

**ℝ is built, it is free, and 7 of the 22 ordered-ring laws hold over it
(`WIP`, agent-creal-laws, 2026-08-18).** ADR-0468 phase R1 is complete and R2 is
most of the way: `CReal` — a Bishop setoid of regular ℚ-sequences — with `Equiv`
**reflexive, symmetric and transitive**, `zero`/`one`/`neg`/`add` with the
`neg`/`add` congruences, and now the **whole additive group plus Bishop's
order**. Thirty-one declarations, every axiom footprint empty, whole trusted
surface **0**:
`cargo run -q -p axeyum-lean-kernel --example creal_setoid_witness`. No
`Quot.sound`, no `funext`, no `propext`; the kernel did not change.

**7 of the 22, and they split into two kinds.** Four hold in `Equiv` form —
`add_comm`, `add_neg` (pointwise, one `Rat` law each through
`Equiv.of_pointwise`) and `add_zero`, `add_assoc` (**not** pointwise: their two
sides are equal at no index, and only `Equiv` can relate them). Three restate
**verbatim** — `le_refl`, `le_trans`, `add_le_add` — because none of them
mentions `Eq`, which is ADR-0468's Measurement 2 cashed.

**`add_zero` and `add_assoc` did not need the missing ℚ lemma.** The previous
costing put both behind `Rat.natDivSucc` antitone in its index (~250 lines).
They are not: the gap in each is a sample at the shifted index `2n+1` compared
with one at `n`, regularity bounds it by `1/(2n+2) + 1/(n+1)` against the
setoid's `2/(n+1)`, and read at the common denominator `2n+2` — which
`natDivSucc_halve` already supplies — that is `3 ≤ 4`, one nonnegative
`1/(2n+2)`. Two helpers carry both laws: `shifted_bound_le` (the inequality) and
`weaken` (widen a `−b ≤ a ∧ a ≤ b` pair). `add_assoc` is then a rearrangement,
not an estimate: `y` is sampled at the SAME index on both sides and cancels
through `rsum_perm`, leaving `(x_M − x_N) + (z_N − z_M)`.

**`CReal.le` is the one-sided reading of `Equiv`, and that is the whole reason
the order was cheap.** `le x y := ∀ n, x_n − y_n ≤ 2/(n+1)`; `Equiv` is
literally `le` both ways, so `le_trans` is `Equiv.trans` with the lower half
deleted — the same four-term estimate at an arbitrary index `j`, now sharing
`telescope_four` and `six_term_bound` with it verbatim (both were extracted from
the existing proof, which still checks), `Rat.add_le_add` in place of
`Rat.bounds_add`, and the same Archimedean lemma. **`le_total` is absent on
purpose**: it holds for ℚ and does not lift, and nothing here assumes it.

**Three guards, each measured, and the example's exit status depends on all of
them.** `CReal.ofRat` (the carrier is inhabited), `Equiv.not_zero_one` (`Equiv`
is not the total relation) and now `not_le_one_zero` (`le` is not either — all
three order laws hold, footprint-free, of the order relating every pair; at
index 3 the claim `1 ≤ 1/2` unfolds through `Int.le` to `Nat.le 2 1`). Two new
negative controls, each measured in both directions: the `add_zero` script with
`CReal.one` for `CReal.zero` is REFUSED, and flipping that one constant back
makes the control test fail because the kernel then accepts; and
`Not (le zero one)` is REFUSED by the identical script that proves
`Not (le one zero)` in the prelude. `le_of_equiv` and
`equiv_of_le_le` pin the order to the setoid: a `le` weakened to `≤ 100/(n+1)`
satisfies all three laws and closes neither.

**The shape that keeps working, from the Archimedean proof and confirmed by
everything since.** No `sub_le_iff` — the gap is written `(−b) + a`. No proof by
contradiction, because `¬¬P → P` does not exist here and is not needed: `Int.le`
is decidable, so `Rat.le_or_lt` is *proved* and any "suppose not" is a case
split. No `Exists` where an index can be computed. And no reasoning about
representations: `rat_prelude/group.rs` derives its 18 lemmas from the 22 laws
alone, never a numerator, which is why `weaken` and `shifted_bound_le` are
theorems of ordered groups plus one `natDivSucc` identity rather than facts
about ℚ's encoding.

**Next, in cost order — and the two cheap strands are gone, so what is left is
genuinely analytic.** The remaining 15 split cleanly: **8 need
`mul`** (`mul_comm`, `mul_assoc`, `mul_one`, `mul_zero`, `left_distrib`,
`mul_nonneg`, `sq_nonneg`, `mul_le_mul_of_nonneg_left` — the last of these needs
`le` as well, which now exists) and **7 need `lt`** (`lt_irrefl`, `lt_trans`,
`lt_of_lt_of_le`, `lt_of_le_of_lt`, `le_of_lt`, `zero_lt_one`,
`add_lt_add_of_le_of_lt`). (a) `mul`, therefore, is worth 8: the blocker is a
canonical bound on a representative derived from
regularity, and this is the one place a Mathlib port will NOT transfer, because
`CauSeq` gets its bound from an *existential* modulus that a fixed modulus does
not supply. Expect to invent. (b) `lt`, the other 7, is harder than
"restate verbatim" suggests — a constructive `<` needs a witness index, so
`Exists` (which the logic prelude has, `exists_elim`), and the naive
`lt x y := ∃ n, y_n − x_n > 2/(n+1)` does NOT give `lt_trans` without a
quantitative gap lemma: the margin is exactly consumed by two regularity round
trips. `lt := Not (le y x)` is a dead end — `le_of_lt` is then not constructive
and `le_total` is unavailable. Budget `lt` as new mathematics, not as
transcription.

**`real: axiom=30` is unchanged, deliberately.** ADR-0468 retires those by
*deletion* in phase R3 — once `generalize_over_ordered_ring` grows an equality
slot and no consumer references the `Real` package — not by exhibiting a model.
Nor is `Eq CReal` the equality of real numbers: `CReal.Equiv` is, `0.999…` and
`1` are distinct `CReal`s and `Equiv`-equal, and every downstream statement will
say so.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `dc72f0bed` | ℝ gets **Bishop's order**: `CReal.le` plus `le_refl`, `le_trans`, `add_le_add` — three of the 22 **verbatim**, none of them mentioning `Eq`. `le_trans` is `Equiv.trans` with the lower half deleted, sharing the extracted `telescope_four`/`six_term_bound` with it. `not_le_one_zero` is the order's discrimination witness (refuted at index 3 by pure reduction) and `le_of_equiv`/`equiv_of_le_le` pin `le` to the setoid. **7 of 22**, 31 declarations, trusted surface still 0. |
| 2026-08-18 | `9e32ab17d` | The **additive group closes**: `add_zero` and `add_assoc` in `Equiv` form — the first two laws that are not pointwise. Neither needs `natDivSucc` antitone in its index, which the previous costing had put in front of them; both reduce to `1/(2n+2) + 1/(n+1) ≤ 2/(n+1)`, i.e. `3 ≤ 4` at the common denominator. **4 of 22**. |
| 2026-08-18 | `fd2759c8b` | ℝ additive structure: `zero`/`one`/`neg`/`add` with Bishop's index shift `(x+y)_n := x_{2n+1} + y_{2n+1}`, the `neg`/`add` congruences, and **2 of the 22** ordered-ring laws in `Equiv` form (`add_comm`, `add_neg`, both pointwise via `Equiv.of_pointwise`). `add_assoc` and `add_zero` are not pointwise; `add_zero` also needs `Rat.natDivSucc` antitone in its index. |
| 2026-08-18 | `ca0e9ea75` | ℝ constructed: `CReal` as a Bishop setoid over ℚ with `Equiv` refl/symm/**trans**, `zero`/`one`/`neg`/`add` and two congruences — 22 declarations, trusted surface **0**, with inhabitation and discrimination witnesses the example's exit status depends on. 2 of the 22 ordered-ring laws hold in `Equiv` form. |
| 2026-08-18 | `f527e7ddb` | The **Archimedean property of ℚ** proved axiom-free (`Rat.le_of_le_add_natDivSucc`), plus a 16-lemma ordered-group toolkit derived from the 22 ring laws alone and the `Rat.add` mirror of `iprod_perm`. Decidability replaces contradiction; the witness index is computed, not searched. |
