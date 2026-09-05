# Lane: power-series — power series with a radius of convergence (W2-5)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, power-series, 2026-09-05).** W2-5 lands eight
declarations in a NEW file
(`crates/axeyum-lean-kernel/src/creal/power_series.rs`), registered at the END
of `creal.rs`'s `STEP_DISPATCH` (225 steps, was 217), with
`scripts/creal-declare-deps.py` reporting 0 order violations and 0 table
disagreements
([ADR-1638](../../research/09-decisions/adr-1638-a-radius-is-a-ratio-witness-and-the-comparison-test-was-already-here.md)).

**The first finding is that most of deliverable 1 already existed**, and the
ADR names it so the next brief can cite it rather than re-derive it a
fourteenth time. `CReal.sumRange_comparisonTest` and
`CReal.sumRange_cauchy_of_dominated` (`series.rs`) are the generic comparison
test; `CReal.geomCauchyOfLt` (`geometric.rs`) is the geometric series with an
explicit modulus; `CReal.mul_sub_one_geom` (`power.rs`) is the closed form,
stated multiplied through as `(1 − x)·Σ_{k<n} xᵏ ~ 1 − xⁿ` because the quotient
form needs a witnessed `PosBound` nothing can manufacture; and
`CReal.sumRangeRatioTest` (`ratio_test.rs`) is the ratio test. Nothing in
deliverable 1 was rebuilt.

What did not exist, and landed here:

1. `CReal.abs_pow_le : ∀ x b, le (abs x) b → ∀ k, le (abs (pow x k)) (pow b k)`
   — the one genuinely new general fact. `CReal.powerSeriesTerm_abs_le` avoids
   it only by assuming `0 ≤ x`; a radius is a claim about `|x| < R`, so the
   signed case needs it. `Nat.rec`, and the step is a *single*
   `abs_mul_le_of_bounds` because `pow`'s ι-reduction already puts the goal in
   that lemma's shape.
2. `CReal.one_pow : ∀ k, Equiv (pow one k) one`.
3. `CReal.powerSeriesPartial : (Nat → CReal) → CReal → Nat → CReal`, built on
   the already-landed `CReal.powerSeriesTerm`.
4. `CReal.powerSeriesTermRadiusBound` — the domination bound.
5. `CReal.powerSeriesCauchyWithinRadius` and
   `CReal.powerSeriesConvergesWithinRadius` — **the radius of convergence**.
6. `CReal.expSeriesPartialIsPowerSeries` and
   `CReal.cosSeriesPartialIsPowerSeries` — the hand-built exponential and
   cosine shelves exhibited as instances of the generic series at the point 1.

**The radius is carried as data, not as a supremum.** `R` is a parameter with
the weighted coefficient bound `∀ k, |a k| · Rᵏ ≤ M`, and "strictly inside" is
a caller-supplied ratio `r` with `0 ≤ r < 1` and `le (abs x) (mul r R)`. Same
decision `geometric.rs` records for `PosBound (1 − x) k`, and forced by the
same fact: over `CReal` the order is undecidable, so a ratio a proof can raise
to the `k`-th power cannot be manufactured from a bare `lt (abs x) R`. `le
zero R` is deliberately **not** a hypothesis — the derivation consumes only
`0 ≤ rᵏ`.

**The instances are proved `Equiv`s, and the reason is symbolic — the obvious
concrete check says the opposite.** At a free `n` both sides are stuck
`Nat.rec`s whose minor premises differ (`expTerm i` against `mul (expTerm i)
(pow one i)` at a bound `i`), so no `Eq.refl` inhabits the equation. But at the
concrete `n = 1` everything is closed and the two sides **are** definitionally
equal. The lane found this by writing the test the obvious way — assert
non-def-eq at `n = 1` — and having it FAIL.
`power_series_tests.rs::exp_instance_is_a_proved_equiv_at_symbolic_n_but_def_eq_at_n_one`
now pins both halves, the concrete one deliberately, as the trap for anyone who
checks one small case and concludes `Eq.refl`.

**Not landed, sized.** Deliverable 4 (termwise addition and scalar multiples
inside a common radius) did not land; it is not blocked — `CReal.sumRange_add`
and `CReal.mul_sumRange` both already exist and the shape is a congruence over
`powerSeriesPartial`, not new analysis. The quotient form of the geometric
closed form (`Σ_{k<n} xᵏ ~ (1 − xⁿ)/(1 − x)` given a `PosBound` witness) is
likewise open and short: `geometric.rs::declare_geom_tail_bounded_div` already
shows the route.
