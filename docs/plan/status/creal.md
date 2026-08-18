# Lane: agent-creal — ℝ constructed, and the ℚ lemmas it needs

<!-- plan-section: lane-status -->

**ℝ is built, and it is free (`WIP`, agent-creal, 2026-08-18).** ADR-0468 phase
R1 is complete and part of R2 is landed: `CReal` — a Bishop setoid of regular
ℚ-sequences — with `Equiv` **reflexive, symmetric and transitive**, plus `zero`,
`one`, `neg`, `add`, and the congruences for `neg` and `add`. Twenty-two
declarations, every axiom footprint empty, whole trusted surface **0**:
`cargo run -q -p axeyum-lean-kernel --example creal_setoid_witness`. No
`Quot.sound`, no `funext`, no `propext`; the kernel did not change.

**Two witnesses stop that zero being vacuous, and the example's exit status
turns on them.** `CReal.ofRat` exhibits a solution of `CReal.Regular`, so the
carrier is not the empty type — all three setoid laws would otherwise hold,
footprint-free, of nothing. `CReal.Equiv.not_zero_one` proves `Equiv` is not the
**total** relation, which is also an equivalence relation; it closes by pure
reduction (at index 3 the lower half is `−1/2 ≤ −1`, which unfolds through
`Int.le` to `Nat.le 1 0`). Measured by mutation: deleting both leaves all other
rows green with empty footprints and the example still exits 1.

**The Archimedean property of ℚ** — `(∀ j, a ≤ b + 6/(j+1)) → a ≤ b`, which
`Equiv.trans` cannot be proved without — came in at about a third of its
estimate, and the three reasons generalise. No `sub_le_iff` (the gap is
`(−b) + a`, produced by translating `b < a` with the proved
`add_lt_add_of_le_of_lt`). No proof by contradiction, because `¬¬P → P` does not
exist here and is not needed: `Int.le` is decidable, so `Rat.le_or_lt` is
*proved* and the argument is a case split — **this is the shape any future ℚ/ℝ
argument wanting "suppose not" should take.** And no `Exists`, because the index
is computed (`k·den c`), not searched for.

**Of the 22 ordered-ring laws, 2 hold in `Equiv` form**: `add_comm` and
`add_neg`. Both are *pointwise* — their two sides sample at the same index — so
`Equiv.of_pointwise` reduces each to one `Rat` law. That bridge (`Eq` pointwise
⟹ `Equiv`, one-way, deliberately) is what makes the pointwise laws nearly free,
and it is worth reaching for first on any remaining law.

**Next, in cost order.** (a) `Rat.natDivSucc` **antitone in its index**
(`j ≤ j' → k/(j'+1) ≤ k/(j+1)`) plus `Rat.bounds_weaken`; that unlocks
`add_zero`, which is not pointwise because `add x zero` samples `x` at `2n+1`
where `x` samples at `n`. (b) `add_assoc`, genuinely analytic: `(x+y)+z` samples
`x` at `2(2n+1)+1` and `x+(y+z)` samples it at `2n+1`. (c) `le`/`lt` and the 13
order laws — ADR-0468's Measurement 2 says these are the fragment Farkas
actually uses and that none of them mentions `Eq`, so they restate verbatim.
(d) `mul`, which is the one place a naive port from Mathlib will not transfer:
it needs a canonical bound on a representative derived from regularity, where
Mathlib gets one from `CauSeq`'s existential modulus.

**`real: axiom=30` is unchanged, deliberately.** ADR-0468 retires those by
*deletion* in phase R3 — once `generalize_over_ordered_ring` grows an equality
slot and no consumer references the `Real` package — not by exhibiting a model.
Nor is `Eq CReal` the equality of real numbers: `CReal.Equiv` is, `0.999…` and
`1` are distinct `CReal`s and `Equiv`-equal, and every downstream statement will
say so.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `fd2759c8b` | ℝ additive structure: `zero`/`one`/`neg`/`add` with Bishop's index shift `(x+y)_n := x_{2n+1} + y_{2n+1}`, the `neg`/`add` congruences, and **2 of the 22** ordered-ring laws in `Equiv` form (`add_comm`, `add_neg`, both pointwise via `Equiv.of_pointwise`). `add_assoc` and `add_zero` are not pointwise; `add_zero` also needs `Rat.natDivSucc` antitone in its index. |
| 2026-08-18 | `ca0e9ea75` | ℝ constructed: `CReal` as a Bishop setoid over ℚ with `Equiv` refl/symm/**trans**, `zero`/`one`/`neg`/`add` and two congruences — 22 declarations, trusted surface **0**, with inhabitation and discrimination witnesses the example's exit status depends on. 2 of the 22 ordered-ring laws hold in `Equiv` form. |
| 2026-08-18 | `f527e7ddb` | The **Archimedean property of ℚ** proved axiom-free (`Rat.le_of_le_add_natDivSucc`), plus a 16-lemma ordered-group toolkit derived from the 22 ring laws alone and the `Rat.add` mirror of `iprod_perm`. Decidability replaces contradiction; the witness index is computed, not searched. |
