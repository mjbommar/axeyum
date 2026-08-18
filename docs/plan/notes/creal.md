# Notes: creal

Detail moved out of [`../status/creal.md`](../status/creal.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The count is read out of the kernel, not asserted here.**
`CRealPrelude::ordered_ring_laws` is the 22 in the `Real` package's own
declaration order — the same order `RatPrelude::ring_laws` uses — and both the
example's exit status and two tests require every entry to be a *distinct*,
checked, footprint-empty `Theorem`. A third test asserts the `CReal` and `Rat`
lists are the same 22 names position by position, so `CReal` cannot quietly drop
`mul_assoc` and repeat `mul_comm` and still report 22. Verified by mutation:
dropping `declare_mul_assoc` flips the example to exit 1 with the matching
message and leaves every other row green.

**22 of 22, and they split into two kinds.** Nine hold in `Equiv` form —
`add_comm`, `add_neg`, `mul_comm`, `mul_zero` (pointwise, one `Rat` law each
through `Equiv.of_pointwise`) and `add_zero`, `add_assoc`, `mul_one`,
`mul_assoc`, `left_distrib` (**not** pointwise: their two sides are equal at no
index, and only `Equiv` can relate them). Thirteen restate **verbatim** —
`le_refl`, `le_trans`, `add_le_add`, `lt_irrefl`, `lt_trans`, `lt_of_lt_of_le`,
`lt_of_le_of_lt`, `le_of_lt`, `zero_lt_one`, `add_lt_add_of_le_of_lt`,
`mul_nonneg`, `sq_nonneg`, `mul_le_mul_of_nonneg_left` — because none of them
mentions `Eq`, which is ADR-0483's Measurement 2 cashed. `mul_congr`, the fifth
congruence obligation and the R4 prerequisite ADR-0483 calls the setoid's real
tax, is proved too; it is not one of the 22.

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

**Seven guards, each measured, and the example's exit status depends on all of
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

**The product needed two guards of its own, and the reason is measured.**
`mul_zero`, `mul_comm` and `sq_nonneg` all hold — footprint-free — of
`fun _ _ => CReal.zero`, exactly as six of the seven strict-order laws held of
the empty relation. So `CReal.ofRat_mul`
(`Equiv (mul (ofRat q) (ofRat r)) (ofRat (q·r))`) pins the *operation* on the
whole embedded ℚ rather than asserting a property of it, and
`CReal.not_equiv_mul_one_one_zero` refuses the constant-zero product by
computation. Verified by mutation, in both directions: dropping
`declare_discrimination` flips the example to exit 1 with the matching message,
leaves every other row green and footprint-empty, and kills exactly three tests;
and the identical script pointed at `Not (Equiv (mul one one) one)` — false,
one constant different — is **REFUSED** by the kernel. The first version of the
presence test read `axiom_footprint` on the witness *without* first checking it
was declared, so it passed with the witness deleted; `axiom_footprint` of an
interned-but-undeclared name is the empty vector, which is the repository's
standing "empty result from a tool never pointed at your subject" trap.

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

**`CReal.mul` is built, and the re-costing was right in both directions.** The
canonical bound *is* cheap: regularity at `n = 0` gives `|x_m − x_0| ≤ 1/(m+1)
+ 1` outright, `Rat.natDivSucc_le_one` turns the first summand into `1`, and
`|x_m| ≤ |x_0| + 2` follows for every `m` with nothing extracted and nothing
chosen. `CReal.bound x := natAbs (num (seq x 0)) + 1` is a **projection**. The
ℕ-valued bridge was exactly the two `Int` facts predicted —
`x ≤ ofNat (natAbs x)` and `−ofNat (natAbs x) ≤ x`, both of which *compute*:
`Int.le` is a four-case definition, so `Int.le (negSucc m) (ofNat (succ m))`
reduces to `True` and the other branch to `Nat.le n n`. The one thing the plan
did not name is that the `ℚ`-level statement (`Rat.bounds_num`) still needs a
cross-multiplication through `normalize_cross`, because `natDivSucc k 0`'s
projections are opaque.

*The estimate closes exactly, with no slack.* `CReal.mulShift x y :=
bound x + bound y + 1`, written as a successor so `c + 1` **is** `Kx + Ky` and
ℕ-subtraction never appears; the index is `(c+1)·n + c`, which is precisely
`natDivSucc_scale`'s. The four terms
`Kx/(A+1) + Kx/(B+1) + Ky/(A+1) + Ky/(B+1)` fuse in the numerator to
`(Kx+Ky)/(A+1) + (Kx+Ky)/(B+1)`, and each of those *is* the regularity bound —
no weakening step, and `Rat.natDivSucc` still never antitone in its index.
`Rat.natDivSucc_mul` (`k/1 · a/(j+1) = k·a/(j+1)`) is what keeps a scaled bound
a single `natDivSucc`; without it the estimate degenerates into a product of two
rationals whose projections are opaque.

*`mul_nonneg` is the one that is genuinely about the order.* `0 ≤ x` over the
reals does **not** say any sample of `x` is non-negative — only that each sits
above `−2/(j+1)` — so the product's lower bound has to trade that residue
against the other factor's canonical magnitude. That is
`Rat.neg_mul_le_of_bounds`, and the resulting `2/(j+1) · (c+1)/1` fuses straight
back to `2/(n+1)`. `sq_nonneg`, by contrast, is free: `x_j·x_j ≥ 0` already
holds in ℚ and the order's slack is never touched.

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

**The last four were one problem, and the fix was to make the constant free.**
`mul_assoc`, `left_distrib`, `mul_le_mul_of_nonneg_left` and `mul_congr` all
compare two products whose **sampling indices differ** — `mul x (add y z)` and
`add (mul x y) (mul x z)` agree at no index and their `mulShift`s are not even
equal as naturals — so `CReal.mul`'s own *exact* estimate is unavailable and the
naive bound is `C/(n+1)` for some `C > 2`. Two new pieces make that enough:

- `CReal.Equiv.of_bounded : (∀ n, |x_n − y_n| ≤ K/(n+1)) → Equiv x y`. **`Equiv`
  only needs the difference to be `O(1/n)`; the constant is free.** It is
  `Equiv.trans`'s argument with one term deleted, and it closes on
  `Rat.le_of_le_add_natDivSucc` — whose numerator is a `Nat` **parameter**, so a
  symbolic `K` built out of the factors' `CReal.bound`s is as acceptable as a
  literal. It is the Archimedean property's *third* consumer.
- `Rat.nat_index_compose : (a+1)·((b+1)·n + b) + a = (D+1)·n + D`. **Bishop's
  sampling indices are closed under composition**, and the additive shift `2n+1`
  *is* the `a = 1` case — so every nested index (`mul` inside `mul`, `add`
  inside `mul`) reads back at `n` through one instance of
  `Rat.natDivSucc_le_scaled`, and no nesting needs arithmetic of its own.

With those, each law is `Rat.mul_sub_mul` plus `Rat.bounds_mul` at one or two
levels, and the constants are pure bookkeeping (`Kx·4 + Ky'·4` for `mul_congr`,
`(Kx·Ky)·2 + Kz·(Kx·2 + Ky·2)` for `mul_assoc`).
`mul_le_mul_of_nonneg_left` needed **no estimate at all**, exactly as costed:
`z − y ≥ 0`, so `x·(z − y) ≥ 0` by `mul_nonneg`, and `left_distrib` plus
`mul_congr` say `x·z` is `Equiv`-equal to `x·y + x·(z − y)`. Doing
`left_distrib` before `mul_assoc` was worth two of the three.

*The cost that did land somewhere.* Type-checking the development is now ~45 s
in a debug build, up from ~9 s, and `mul_assoc`/`left_distrib` are most of it —
their proof terms nest `product_gap` inside `product_gap`. The `creal` test
module builds one template and clones it (`prelude_cache`'s argument verbatim;
`creal_prelude_builds` still does a real build), which took the module from
140 s back to 75 s. `PreludeKey` has no `CReal` variant, so
`crate::prelude_cache` does not cover it; that is the next lever if this becomes
a gate problem.

**`real: axiom=30` is unchanged, deliberately.** ADR-0483 retires those by
*deletion* in phase R4 — once `generalize_over_ordered_ring` grows an equality
slot and no consumer references the `Real` package — not by exhibiting a model.
Nor is `Eq CReal` the equality of real numbers: `CReal.Equiv` is, `0.999…` and
`1` are distinct `CReal`s and `Equiv`-equal, and every downstream statement will
say so.

## Archived landed-changes rows

| 2026-08-18 | `de85ba7ff` | ℝ gets **multiplication**: `CReal.mul` at Bishop's product index `(c+1)·n + c` with `c := bound x + bound y + 1`, plus `CReal.bound` (a *projection*, `natAbs (num (seq x 0)) + 1`) and `bound_within`. Five of the 22 land — `mul_comm`, `mul_one`, `mul_zero` in `Equiv` form, `mul_nonneg` and `sq_nonneg` **verbatim** — taking it to **19 of 22**, 53 declarations, trusted surface still 0. The canonical bound is cheap after all: the fixed modulus bounds every sample by `\|x_0\| + 2` at `n = 0` with nothing to extract, and the ℕ bridge is two computing `Int.natAbs` facts. The estimate closes **exactly** — the four product terms fuse to the regularity bound with no weakening step — and `Rat.natDivSucc` is still never needed antitone in its index. Eleven new ℚ lemmas (`bounds_mul`, `neg_mul_le_of_bounds`, `mul_sub_mul`, `natDivSucc_mul`, `natDivSucc_le_one`, `bounds_num`, …), all axiom-free. `ofRat_mul` + `not_equiv_mul_one_one_zero` are the product's discrimination witnesses, verified load-bearing by deletion (three tests die, every other row stays green) and by a refused negative control. |
| 2026-08-18 | `PENDING2` | `Rat.natDivSucc_scale` and `Rat.natDivSucc_le_add_left`: the two ℚ lemmas that take **`natDivSucc` antitone in its index** off `CReal.mul`'s path. `scale` generalises `natDivSucc_halve` to an arbitrary factor (`halve` is its `c = 1` instance definitionally, and the kernel is asked to confirm the subsumption, not a doc comment); `le_add_left` is monotonicity in the numerator, stated additively so ℕ-subtraction never appears. Together `1/(K(n+1)) ≤ 1/(n+1)` becomes `1 ≤ K` at one denominator, for **any** K — which is what the fixed-shift trick behind `add_zero`/`add_assoc` was thought not to generalise to. |
| 2026-08-18 | `PENDING` | ℝ gets the **strict order**: `CReal.lt x y := ∃ (q : Rat), 0 < q ∧ le (add x (ofRat q)) y` — the gap carried as a rational rather than recomputed as an index, which is what makes `lt_trans` work where the naive `∃ n, y_n − x_n > 2/(n+1)` cannot. Seven of the 22 land **verbatim** (`lt_irrefl`, `lt_trans`, `lt_of_lt_of_le`, `lt_of_le_of_lt`, `le_of_lt`, `zero_lt_one`, `add_lt_add_of_le_of_lt`), plus `le_add_of_nonneg` and the `le_congr`/`lt_congr` the R4 equality slot asks for. `lt_irrefl` is the Archimedean property's second consumer; `zero_lt_one` + `lt_irrefl` are the strict order's discrimination witnesses and the example's exit status depends on both (verified by deleting each). **14 of 22**, 42 declarations, trusted surface still 0. |
| 2026-08-18 | `dc72f0bed` | ℝ gets **Bishop's order**: `CReal.le` plus `le_refl`, `le_trans`, `add_le_add` — three of the 22 **verbatim**, none of them mentioning `Eq`. `le_trans` is `Equiv.trans` with the lower half deleted, sharing the extracted `telescope_four`/`six_term_bound` with it. `not_le_one_zero` is the order's discrimination witness (refuted at index 3 by pure reduction) and `le_of_equiv`/`equiv_of_le_le` pin `le` to the setoid. **7 of 22**, 31 declarations, trusted surface still 0. |
| 2026-08-18 | `9e32ab17d` | The **additive group closes**: `add_zero` and `add_assoc` in `Equiv` form — the first two laws that are not pointwise. Neither needs `natDivSucc` antitone in its index, which the previous costing had put in front of them; both reduce to `1/(2n+2) + 1/(n+1) ≤ 2/(n+1)`, i.e. `3 ≤ 4` at the common denominator. **4 of 22**. |
| 2026-08-18 | `fd2759c8b` | ℝ additive structure: `zero`/`one`/`neg`/`add` with Bishop's index shift `(x+y)_n := x_{2n+1} + y_{2n+1}`, the `neg`/`add` congruences, and **2 of the 22** ordered-ring laws in `Equiv` form (`add_comm`, `add_neg`, both pointwise via `Equiv.of_pointwise`). `add_assoc` and `add_zero` are not pointwise; `add_zero` also needs `Rat.natDivSucc` antitone in its index. |
| 2026-08-18 | `ca0e9ea75` | ℝ constructed: `CReal` as a Bishop setoid over ℚ with `Equiv` refl/symm/**trans**, `zero`/`one`/`neg`/`add` and two congruences — 22 declarations, trusted surface **0**, with inhabitation and discrimination witnesses the example's exit status depends on. 2 of the 22 ordered-ring laws hold in `Equiv` form. |
| 2026-08-18 | `f527e7ddb` | The **Archimedean property of ℚ** proved axiom-free (`Rat.le_of_le_add_natDivSucc`), plus a 16-lemma ordered-group toolkit derived from the 22 ring laws alone and the `Rat.add` mirror of `iprod_perm`. Decidability replaces contradiction; the witness index is computed, not searched. |
