# Lane: int-order-two-squares — two thirds of the recorded obstruction was already stale

<!-- plan-section: lane-status -->

**The ordering half of Fermat's two-square descent is built** (`DONE`,
int-order-two-squares, 2026-09-05). W3-10's first slice (ADR-1633) sized the
remaining obstruction as "this prelude has no `Int` absolute-value order lemmas
at all: `natAbs_le_iff`, `mul_le_mul` over ℤ and `sq_le_sq` do not [exist]".
Re-measured on 2026-09-05 with a freshly built `shape_search`
(`declarations=3236`, positive control `Int.descentStep` FOUND, so the index
post-dates the merge that added it): **two of those three already existed.**
`Int.nat_abs_le_iff_mul_self_le` landed 2026-09-01 in `nat_abs_mirrors.rs` when
the `integer-absolute-value` held-out family was drawn and scored, and
`Int.mul_le_mul_of_nonneg_left` was already declared. Only `sq_le_sq` was
genuinely absent, and the real gap was not a name at all — it was the **shape**
of the bound.

`int_prelude/order_squares.rs` lands 23 axiom-free laws (ADR-1647): the
sign/negation plumbing, halving (`le_of_add_le_add_self`) and left cancellation
(`le_of_mul_le_mul_left`, `lt_of_mul_lt_mul_left`), the two-sided square bound
`sq_le_sq_of_neg_le_of_le`, the bounded representative
`exists_centered_representative`, the strict decrease
`sq_add_sq_lt_sq_of_bounds`, and the descent's termination certificate
`descentMultiplierBounds`, which takes the FACTORISATION `m*q = c² + e²` rather
than the measure and returns `0 ≤ q ∧ q < m`.

Every bound is spelled `Int.add c c`, never `Int.mul (ofNat 2) c`. The two are
equal; the `add` form is the one the existing shelf can move (doubling an
inequality is `Int.add_le_add h h`), and it removes every numeral from the
halving step, which is the only division in the whole argument.

**`Int.fermatTwoSquares` did NOT land.** Four pieces remain, all sized in the
notes of `F:int-fermat-two-squares` and none blocked on a missing capability:
the entry step from `Int.firstSupplementaryLawResidue`; the divisibility
`m ∣ c² + e²` that produces the new multiplier; the `q ≠ 0` argument (the only
step that consumes primality); and the `Nat.strongInduction` assembly. One
correction recorded there and in ADR-1647: `two_squares.rs`'s module doc says
the entry point `declare_exists_mul_isSumOfTwoSquares_of_residue` already
landed — **it does not exist**, the name occurs once in that doc comment and is
not in `declare_two_squares_all`.

Three real defects the kernel found and this lane fixed:
`Int.add_le_add_iff_left` binds `(b, c, a)`, so the shared term is its LAST
argument (three call sites got it wrong), and one `isymm` had its equation ends
swapped.

<!-- plan-section: landed-changes -->

| 2026-09-05 | `5aa098f1b` | `int_prelude/order_squares.rs`: the ℤ order shelf as 18 laws — sign/negation plumbing, halving, left cancellation, the two-sided square bound, the centered representative, the strict decrease. Bounds spelled `add c c`, not `mul (ofNat 2) c`. Held-out rows (`integer-natcast`'s `mul_le_mul_of_*`, `descent-and-well-ordering`'s `lt_of_sum_four_squares_eq_mul`) named in the module doc and NOT declared. |
| 2026-09-05 | `81e9fff1f` | `order_squares_tests.rs`: the statement pin rebuilds all 23 `∀`-telescoped types and compares against the ENVIRONMENT-stored type (an axiom-footprint sweep cannot see a weakened bound); `contains` before `axiom_footprint`; both signs of the square bound admitted and both out-of-band arguments refused; both branches of the centered representative pinned at `m = 5` with `c = 3` refused. `derived_laws` 294 → 312, recounted. |
| 2026-09-05 | `ee00002dc` | `Int.descentMultiplierBounds` and four supporting laws (`lt_of_mul_lt_mul_left`, `nonneg_of_mul_nonneg_left`, `pos_of_mul_pos_left`, `eq_zero_of_sq_add_sq_eq_zero`). All five admitted on the first attempt. `derived_laws` 312 → 317. Worked instance `5*1 = 2² + 1²` certifies `0 ≤ 1 ∧ 1 < 5`; `q = 2` REFUSED even though `0 ≤ 2 ∧ 2 < 5` is true. |
