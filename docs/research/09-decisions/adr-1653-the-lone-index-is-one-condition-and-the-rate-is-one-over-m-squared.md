# ADR-1653: Four-wise uncorrelatedness is ONE lone-index condition plus a factoring one, and the rate it buys is 1/m²

Status: accepted
Date: 2026-09-06
Index-summary: The next bounded concentration rate after Chebyshev lands at ℚ. `Rat.FourwiseUncorrelated` is stated as exactly two conditions on an already-centred family — every mixed fourth moment with a LONE index vanishes, and the squares are uncorrelated — because the lone-index form already covers all three unpaired multinomial shapes (`a b c l` distinct, `a a b c`, `a a a l`), so it is one universal and not three. The whole proof runs on one hypothesis-free lemma, `Rat.expectation_sumVars_mul : E[(Σ Y_i)·W] = Σ E[Y_i·W]` for ARBITRARY `W` — including a `W` that mentions the sum being peeled, which is what makes one lemma serve `E[Σ³z]`, `E[Σz³]` and (with its own induction) `E[Σ²z²]`. The bound is written with `sumRange` and not `m·M₄`, because `sumRange f (succ b) ≡ sumRange f b + f b` is `Eq.refl` here while `natDivSucc (succ b) 0 = natDivSucc b 0 + 1` is a rational-numeral fact the prelude does not have. The induction closes with `3σ⁴` of SLACK, not on the nose. Hoeffding stays blocked for the two reasons ADR-1631 recorded, unchanged.
Index-status: accepted

- **Lane**: `fourth-moment` (roadmap W3-12, second slice)
- **Follows**: [ADR-1616](adr-1616-independence-is-not-expressible-so-the-hypothesis-is-uncorrelatedness.md)
  and [ADR-1631](adr-1631-the-binomial-is-a-sum-of-bernoullis-and-hoeffding-needs-a-joint-law.md),
  which named this as the next statable rate.

## Context

ADR-1631 closed with a sized obstruction, not a gap in effort: Hoeffding needs
`E[∏_j f(X_j)] = ∏_j E[f(X_j)]`, a statement about a JOINT law over a product
space, and this development has one weight function over one index range; and
Hoeffding's lemma needs `expFn_add`, which exists on no carrier here. It also
named what IS reachable: `E[(Σ − EΣ)⁴] ≤ 3(mσ²)²` under a four-wise
uncorrelatedness hypothesis, statable because it constrains covariance-like
quantities rather than a joint law.

This ADR records the four design calls that decided the shape of that slice.

## Decision

### 1. The hypothesis is TWO conditions, and the first one is a single universal

`Rat.FourwiseUncorrelated Y m p n` is an `And` of

1. `∀ a b c l < m, a ≠ l → b ≠ l → c ≠ l → E[Y_a Y_b Y_c Y_l] = 0`, and
2. `∀ i j < m, i ≠ j → E[Y_i² Y_j²] = E[Y_i²]·E[Y_j²]`,

stated over an already-CENTRED family (the intended instance is
`Y i := fun k => X i k − E[X i]`).

The obvious spelling would have been three separate vanishing conditions, one
for each shape the multinomial expansion produces with an unpaired index: all
four indices distinct, `a a b c`, and `a a a l`. **One condition covers all
three**, because "some index occurs exactly once" is, after a commutative
reordering, exactly "the index in the last slot differs from the other three".
Every expansion term is rewritten into that canonical left-nested shape by a
`ring::rat` identity before the hypothesis is applied, which is why the
association order can be fixed once and the disequalities only ever have to be
supplied against the last slot.

Independence would imply both conditions. Independence is not expressible here,
so this is the honest weaker hypothesis — the same role
`Rat.PairwiseUncorrelated` plays for the variance of a sum, one moment up.

### 2. The whole proof runs on ONE hypothesis-free peeling lemma

`Rat.expectation_sumVars_mul : E[(Σ_{i<m} Y_i)·W] = Σ_{i<m} E[Y_i·W]` carries
no hypothesis at all: not `IsDistribution`, not uncorrelatedness, not a bound
on `W`. That `W` is arbitrary is the load-bearing part — in every use below,
`W` MENTIONS the sum it is being peeled out of, so the same lemma applied three
times nested turns `E[Σ³·z]` into a triple sum of mixed moments, and applied
once turns `E[Σ·z³]` into a single one. Its `= zero` companion
(`Rat.expectation_sumVars_mul_eq_zero`) closes through
`Rat.sumRange_eq_zero_of_lt`, the BOUNDED form, because four-wise
uncorrelatedness supplies zeros only inside its own range and
`sumRange_congr`'s unrestricted hypothesis is therefore unusable.

### 3. `Rat.sumRange_delta` cannot extract the surviving diagonal

`E[Σ²·z²]` is the one cross term the fourth power does not kill, and the
textbook route to it is a double sum whose off-diagonal vanishes. The
repository has `Rat.sumRange_delta` for exactly that — and it is **unusable
here**: its hypothesis is UNRESTRICTED (`∀ t, t ≠ i → f t = 0`, not
`∀ t, t < n → t ≠ i → …`), while the vanishing facts on hand hold only below
the bound. The measured consequence is that `Rat.expectation_sq_sumVars_mul_sq`
is its own induction rather than two peels plus a delta collapse: the successor
step splits `(Σ_{i<j+1})²z² = (Σ_{i<j})²z² + 2(Σ_{i<j})Y_j z² + Y_j²z²` by a
ring identity and kills the middle with the peeling lemma, so the diagonal is
never separated from a rectangle at all.

A `sumRange_delta_lt` with the bounded hypothesis would be a genuinely useful
addition to `rat_prelude/sum.rs`; it was not needed once the induction above
existed, and is left as a note rather than a claim.

### 4. The bound is spelled with `sumRange`, and the induction closes with slack

The conclusion is `E[(Σ_{i<m} Y_i)⁴] ≤ Σ_{i<m} M₄ + 3(Σ_{i<m} σ²)²` and not
`m·M₄ + 3m²σ⁴`. The reason is mechanical: `Rat.sumRange f (succ b) ≡
sumRange f b + f b` is `Eq.refl` in this prelude, so the successor step of the
induction receives the shape of its own target definitionally, whereas
`Rat.natDivSucc (succ b) 0 = natDivSucc b 0 + Rat.one` is a rational-numeral
fact this prelude does not carry. `Rat.sum_range_const` converts either constant
sum to the `m·c` form at the point of use. The `3` is three summands for the
same reason `ring::rat` spells every coefficient additively.

The induction does **not** close on the nose. At stage `b+1` the accumulated
bound is `Σ_b M₄ + 3T² + 6Tσ² + M₄` against a target of
`Σ_b M₄ + M₄ + 3(T+σ²)²`, and the difference is exactly `3σ⁴`. So the last step
is `Rat.add_le_add` against `Rat.sq_nonneg`, followed by one `ring::rat`
rebalancing — not an equality. Recording this because the natural first attempt
is to look for the exact identity `Σ E[Y_i⁴] + 3 Σ_{i≠j} E[Y_i²]E[Y_j²]`, which
needs an off-diagonal double sum this shelf has no comfortable way to state,
and is not needed for the rate.

## Consequences

- The tail `Rat.fourth_moment_tailSumVars` decays like **1/m²** in the sample
  size, against Chebyshev's 1/m on the same shelf
  (`Rat.chebyshev_sampleMean_uncorrelated`). That is the first Hoeffding-class
  rate this carrier can state, and the gap is the whole return on paying for
  the fourth moment.
- It is stated on the SUM at threshold `a`, which is the sample mean at
  threshold `a/m`; no `Rat.inv` is introduced anywhere, matching every other
  tail bound on this shelf.
- The indicator keeps the deviation form `Σ − E Σ` untouched. Only the
  right-hand expectation is rewritten to `E[Σ⁴]` (through the per-variable
  centring hypothesis), because rewriting under the `Rat.indicator` binder
  would need function extensionality this kernel does not have.
- **Hoeffding is unchanged.** Both obstructions ADR-1631 recorded were
  re-checked and still hold; nothing in this slice moves them.
