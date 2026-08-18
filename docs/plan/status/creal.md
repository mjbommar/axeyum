# Lane: agent-creal-laws — ℝ constructed, and the ordered-ring laws over it

<!-- plan-section: lane-status -->

**ℝ is built, it is free, and 14 of the 22 ordered-ring laws hold over it —
the 8 that remain are exactly the 8 that mention `mul`
(`WIP`, agent-creal-mul-lt, 2026-08-18).** ADR-0468 phase R1 is complete and R2
is most of the way: `CReal` — a Bishop setoid of regular ℚ-sequences — with
`Equiv` **reflexive, symmetric and transitive**, `zero`/`one`/`neg`/`add` with
the `neg`/`add` congruences, and now the **whole additive group, Bishop's order
and the strict order over it**. Forty-two declarations, every axiom footprint
empty, whole trusted surface **0**:
`cargo run -q -p axeyum-lean-kernel --example creal_setoid_witness`. No
`Quot.sound`, no `funext`, no `propext`; the kernel did not change.

**14 of the 22, and they split into two kinds.** Four hold in `Equiv` form —
`add_comm`, `add_neg` (pointwise, one `Rat` law each through
`Equiv.of_pointwise`) and `add_zero`, `add_assoc` (**not** pointwise: their two
sides are equal at no index, and only `Equiv` can relate them). Ten restate
**verbatim** — `le_refl`, `le_trans`, `add_le_add`, `lt_irrefl`, `lt_trans`,
`lt_of_lt_of_le`, `lt_of_le_of_lt`, `le_of_lt`, `zero_lt_one`,
`add_lt_add_of_le_of_lt` — because none of them mentions `Eq`, which is
ADR-0468's Measurement 2 cashed.

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

**`CReal.lt` quantifies over the GAP, not over an index, and that is the whole
reason the other 7 came in as rearrangements.** `lt x y := ∃ (q : Rat), 0 < q ∧
le (add x (ofRat q)) y`. Both shapes the previous costing named are confirmed
dead and neither had to be walked: `lt := Not (le y x)` makes `le_of_lt`
non-constructive with no `le_total` over ℝ to recover it from, and
`∃ n, y_n − x_n > 2/(n+1)` fails `lt_trans` because composing two witnesses
needs a NEW index and the two regularity round trips reaching it consume the
margin exactly — chained at a third index the estimate is
`z_k − x_k > −2/(k+1) − 1/(m+1) − 1/(n+1)`, negative for every choice. Carrying
the rational gap removes the recomputation: `lt_trans` hands `q₁` through
untouched and reads its second hypothesis only through `le_of_lt`. So the
costing was right about the *definition* and wrong about the *proofs* —
`lt_of_lt_of_le`, `lt_of_le_of_lt`, `le_of_lt`, `lt_trans` and
`add_lt_add_of_le_of_lt` are `le_trans`/`add_le_add`/`add_assoc`
rearrangements, and only `lt_irrefl` is an estimate. It is the Archimedean
property's **second** consumer: a witness for `x < x` forces `q ≤ 4/(n+1)` at
every `n`, hence `q ≤ 0`, contradicting `0 < q` — with no double negation, the
contradiction being `Rat.lt_irrefl` on `Rat.lt_of_lt_of_le`. The one analytic
step is `le_add_of_nonneg` (`0 ≤ q → x ≤ x + q`), analytic only because of the
index shift, and it closes on `shifted_bound_le`, the same inequality
`add_zero` and `add_assoc` reduce to.

**Five guards, each measured, and the example's exit status depends on all of
them.** `CReal.ofRat` (the carrier is inhabited), `Equiv.not_zero_one` (`Equiv`
is not the total relation), `not_le_one_zero` (`le` is not either — all three
`le` laws hold, footprint-free, of the order relating every pair; at index 3 the
claim `1 ≤ 1/2` unfolds through `Int.le` to `Nat.le 2 1`), and now
`zero_lt_one` **and** `lt_irrefl` together: six of the seven strict-order laws
only CONSUME a `lt`, so all six hold — footprint-free — of the EMPTY relation,
and `zero_lt_one` is the only one that exhibits an inhabitant while `lt_irrefl`
is the only one that refuses a pair. Verified by mutation, not asserted:
dropping `declare_zero_lt_one` and then `declare_lt_irrefl` each flips the
example to exit 1 with the matching message and every other row still green and
footprint-empty. Three negative controls, each measured in both directions: the
`add_zero` script with `CReal.one` for `CReal.zero` is REFUSED; `Not (le zero
one)` is REFUSED by the identical script that proves `Not (le one zero)`; and
the `zero_lt_one` script with its two constants swapped is REFUSED as
`lt one zero`. `le_of_equiv` and `equiv_of_le_le` pin the order to the setoid: a
`le` weakened to `≤ 100/(n+1)` satisfies all three laws and closes neither.

**`le_congr` and `lt_congr` are built too — not among the 22, but two of the
nine equality-slot binders R4 asks for by name.** Neither is an estimate:
`le_congr` is `le_of_equiv` on each side plus two `le_trans`, and `lt_congr`
moves the same rational gap across an `add_congr`.

**The shape that keeps working, from the Archimedean proof and confirmed by
everything since.** No `sub_le_iff` — the gap is written `(−b) + a`. No proof by
contradiction, because `¬¬P → P` does not exist here and is not needed: `Int.le`
is decidable, so `Rat.le_or_lt` is *proved* and any "suppose not" is a case
split. No `Exists` where an index can be computed. And no reasoning about
representations: `rat_prelude/group.rs` derives its 18 lemmas from the 22 laws
alone, never a numerator, which is why `weaken` and `shifted_bound_le` are
theorems of ordered groups plus one `natDivSucc` identity rather than facts
about ℚ's encoding.

**Next, and it is now a single strand: `mul`, worth all 8 remaining laws**
(`mul_comm`, `mul_assoc`, `mul_one`, `mul_zero`, `left_distrib`, `mul_nonneg`,
`sq_nonneg`, `mul_le_mul_of_nonneg_left`). Two of its three blockers were
removed this session, and the third was re-costed downward — the whole thing is
now a bounded job rather than an open question.

*What the fixed modulus actually costs, measured rather than assumed.* The
canonical bound is **cheap**, not expensive: regularity at `n = 0` gives
`|x_m − x_0| ≤ 1/(m+1) + 1 ≤ 2` outright, so `|x_m| ≤ |x_0| + 2` for every `m`
with no modulus to extract. That is the opposite of the received costing, which
said `CauSeq`'s existential modulus supplies something a fixed one does not.
What a fixed modulus genuinely does not supply is the **ℕ-valued** `K` that
Bishop's sampling index needs, and the cheapest bridge is not a ceiling function
at all: `q ≤ ofNat (Int.natAbs (Rat.num q))` whenever `1 ≤ den q`, which is two
`Int` facts and no division. Price that before writing any `mul` proof.

*The antitonicity blocker is gone.* Every `mul` law compares `1/(K(n+1))` with
`1/(n+1)`, and the trick that saved `add_zero`/`add_assoc` — read both at a
common denominator — was believed not to generalise because `mul` has no fixed
shift. It does generalise, and both halves are now built and axiom-free:
`Rat.natDivSucc_scale : natDivSucc (c+1) ((c+1)·m + c) = natDivSucc 1 m`
(`natDivSucc_halve` is its `c = 1` instance **definitionally**, and the kernel
is asked to confirm that in `nat_div_succ_scale_subsumes_halve_…` rather than a
doc comment asserting it), and
`Rat.natDivSucc_le_add_left : natDivSucc a j ≤ natDivSucc (a+e) j` — monotone in
the *numerator*, stated additively so ℕ-subtraction never appears. Together they
turn `1/(K(n+1)) ≤ 1/(n+1)` into `1 ≤ K` at one denominator. **`Rat.natDivSucc`
antitone in its index — the ~250-line lemma dodged twice — is not needed for
`mul` either**, and on current evidence should stay unbuilt.

*What is left.* The ℚ-level `bounds_mul`, `neg_mul` and
`mul_le_mul_of_nonneg_right` (all from the 22 laws plus a `le_or_lt` case
split), the bound function `CReal.bound x := natAbs (num (seq x 0)) + 2` with
`Within (seq x m) (natDivSucc (bound x) 0)`, then `CReal.mul` with
`(xy)_n := x_{j(n)}·y_{j(n)}` at `j(n) = K·(n+1) − 1`, its congruence, and the
eight laws. `mul` also needs its own **discrimination witness** for the same
reason `lt` did — `mul_zero`, `mul_one` and `sq_nonneg` all hold of a `mul` that
returns `zero` on everything.

**`real: axiom=30` is unchanged, deliberately.** ADR-0468 retires those by
*deletion* in phase R3 — once `generalize_over_ordered_ring` grows an equality
slot and no consumer references the `Real` package — not by exhibiting a model.
Nor is `Eq CReal` the equality of real numbers: `CReal.Equiv` is, `0.999…` and
`1` are distinct `CReal`s and `Equiv`-equal, and every downstream statement will
say so.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `PENDING2` | `Rat.natDivSucc_scale` and `Rat.natDivSucc_le_add_left`: the two ℚ lemmas that take **`natDivSucc` antitone in its index** off `CReal.mul`'s path. `scale` generalises `natDivSucc_halve` to an arbitrary factor (`halve` is its `c = 1` instance definitionally, and the kernel is asked to confirm the subsumption, not a doc comment); `le_add_left` is monotonicity in the numerator, stated additively so ℕ-subtraction never appears. Together `1/(K(n+1)) ≤ 1/(n+1)` becomes `1 ≤ K` at one denominator, for **any** K — which is what the fixed-shift trick behind `add_zero`/`add_assoc` was thought not to generalise to. |
| 2026-08-18 | `PENDING` | ℝ gets the **strict order**: `CReal.lt x y := ∃ (q : Rat), 0 < q ∧ le (add x (ofRat q)) y` — the gap carried as a rational rather than recomputed as an index, which is what makes `lt_trans` work where the naive `∃ n, y_n − x_n > 2/(n+1)` cannot. Seven of the 22 land **verbatim** (`lt_irrefl`, `lt_trans`, `lt_of_lt_of_le`, `lt_of_le_of_lt`, `le_of_lt`, `zero_lt_one`, `add_lt_add_of_le_of_lt`), plus `le_add_of_nonneg` and the `le_congr`/`lt_congr` the R4 equality slot asks for. `lt_irrefl` is the Archimedean property's second consumer; `zero_lt_one` + `lt_irrefl` are the strict order's discrimination witnesses and the example's exit status depends on both (verified by deleting each). **14 of 22**, 42 declarations, trusted surface still 0. |
| 2026-08-18 | `dc72f0bed` | ℝ gets **Bishop's order**: `CReal.le` plus `le_refl`, `le_trans`, `add_le_add` — three of the 22 **verbatim**, none of them mentioning `Eq`. `le_trans` is `Equiv.trans` with the lower half deleted, sharing the extracted `telescope_four`/`six_term_bound` with it. `not_le_one_zero` is the order's discrimination witness (refuted at index 3 by pure reduction) and `le_of_equiv`/`equiv_of_le_le` pin `le` to the setoid. **7 of 22**, 31 declarations, trusted surface still 0. |
| 2026-08-18 | `9e32ab17d` | The **additive group closes**: `add_zero` and `add_assoc` in `Equiv` form — the first two laws that are not pointwise. Neither needs `natDivSucc` antitone in its index, which the previous costing had put in front of them; both reduce to `1/(2n+2) + 1/(n+1) ≤ 2/(n+1)`, i.e. `3 ≤ 4` at the common denominator. **4 of 22**. |
| 2026-08-18 | `fd2759c8b` | ℝ additive structure: `zero`/`one`/`neg`/`add` with Bishop's index shift `(x+y)_n := x_{2n+1} + y_{2n+1}`, the `neg`/`add` congruences, and **2 of the 22** ordered-ring laws in `Equiv` form (`add_comm`, `add_neg`, both pointwise via `Equiv.of_pointwise`). `add_assoc` and `add_zero` are not pointwise; `add_zero` also needs `Rat.natDivSucc` antitone in its index. |
| 2026-08-18 | `ca0e9ea75` | ℝ constructed: `CReal` as a Bishop setoid over ℚ with `Equiv` refl/symm/**trans**, `zero`/`one`/`neg`/`add` and two congruences — 22 declarations, trusted surface **0**, with inhabitation and discrimination witnesses the example's exit status depends on. 2 of the 22 ordered-ring laws hold in `Equiv` form. |
| 2026-08-18 | `f527e7ddb` | The **Archimedean property of ℚ** proved axiom-free (`Rat.le_of_le_add_natDivSucc`), plus a 16-lemma ordered-group toolkit derived from the 22 ring laws alone and the `Rat.add` mirror of `iprod_perm`. Decidability replaces contradiction; the witness index is computed, not searched. |
