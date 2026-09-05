# ADR-1638: a radius of convergence is a ratio witness, and the comparison test was already here

Status: proposed
Date: 2026-09-05
Lane: `power-series`
Roadmap: W2-5 (power series with a radius of convergence)

Index-summary: The brief's deliverable 1 — a generic comparison test, the
geometric series, and a ratio-style bound — was **already landed** and is named
here so the next lane does not rebuild it a third time:
`CReal.sumRange_comparisonTest` and `CReal.sumRange_cauchy_of_dominated`
(`series.rs`), `CReal.geomCauchyOfLt` and `CReal.mul_sub_one_geom`
(`geometric.rs` / `power.rs`), and `CReal.sumRangeRatioTest` with
`CReal.geomScaledCauchyOfLt` (`ratio_test.rs`). What did **not** exist is the
partial-sum function and any statement of a radius. `CReal.powerSeriesPartial`
is defined on the already-landed `CReal.powerSeriesTerm`, and the radius lands
as `CReal.powerSeriesCauchyWithinRadius` / `...ConvergesWithinRadius` with the
radius carried as **data** — a caller-supplied ratio `r` with `0 ≤ r < 1` and
the point hypothesis `le (abs x) (mul r R)` — not as a supremum, for the same
reason `geometric.rs` carries `PosBound (1 − x) k` rather than deriving it. The
signed case forced one genuinely new general lemma, `CReal.abs_pow_le`, because
`CReal.powerSeriesTerm_abs_le` avoids `|xᵏ| ≤ bᵏ` only by assuming `0 ≤ x`, and
a radius is a claim about `|x| < R`. The exp and cos shelves are exhibited as
instances by `CReal.expSeriesPartialIsPowerSeries` /
`CReal.cosSeriesPartialIsPowerSeries`, and these are **proved `Equiv`s, not
`Eq.refl`** — measured, not asserted, by a test that shows the two sides are
not definitionally equal at `n = 1`.

Index-status: proposed

## Context

The brief for this lane asked for four things: a generic comparison test, the
geometric series with an explicit modulus and a ratio-style bound; a
`powerSeriesPartial` with a radius of convergence; `exp` and `cos` re-derived as
instances; and, if those landed, termwise addition and scalar multiples.

The first thing the lane measured was that most of deliverable 1 was already in
the tree. `CLAUDE.md`'s standing warning applies exactly — a name search does not
find these because there is no single spelling, and the `creal` names are split
across `creal.rs`'s own 600-plus-field struct and seventeen per-module
registries. Enumerating every `kernel.name_str(creal, "…")` across `creal.rs`
and `creal/*.rs` returned 738 names, and among them:

| brief asked for | already declared | where |
| --- | --- | --- |
| comparison test | `CReal.sumRange_comparisonTest`, `CReal.sumRange_cauchy_of_dominated`, `CReal.sumRange_converges_of_dominated` | `creal/series.rs` |
| geometric series, explicit modulus | `CReal.geomCauchyOfLt`, `CReal.geom_tail_bounded_div` | `creal/geometric.rs` |
| geometric closed form | `CReal.mul_sub_one_geom` — `(1 − x)·Σ_{k<n} xᵏ ~ 1 − xⁿ` | `creal/power.rs` |
| ratio-style bound | `CReal.sumRangeRatioTest`, `CReal.geomScaledCauchyOfLt`, `CReal.ratio_decay_bound` | `creal/ratio_test.rs` |
| power series term | `CReal.powerSeriesTerm`, `_congr`, `_abs_le` | `creal/power.rs` |

Rebuilding any of these would have been the fourteenth measured instance of a
lane re-deriving what existed. This ADR records them by name so the next brief
can cite them.

Two things in that table need reading carefully rather than counting.

**The geometric closed form is stated multiplied through, on purpose.**
`CReal.mul_sub_one_geom` gives `(1 − x)·Σ_{k<n} xᵏ ~ 1 − xⁿ`, not `Σ xᵏ ~ (1 −
xⁿ)/(1 − x)`. `power.rs`'s own documentation gives the reason: the quotient form
needs `CReal.inv (1 − x)`, which needs a *witnessed* `PosBound`, and no theorem
can manufacture one for an arbitrary `x` — over `CReal` the order is
undecidable, `Apart` is an `Or` that does not eliminate into `Type`, and this
kernel has no Markov principle. The multiplied form holds for every `x`,
including `x ~ 1` where the quotient form is meaningless. Note also that the
exponent in the brief (`1 − r^(n+1)`) does not match this kernel's `sumRange`,
which is a sum over `k < n`; the correct exponent is `n`.

**`CReal.powerSeriesTerm_abs_le` is not a radius bound.** Its hypotheses are an
*unweighted* coefficient bound `|c j| ≤ M` and `0 ≤ x ≤ r`. It is the M-test's
domination package on `[0, r]`, and its `0 ≤ x` is what lets it route `abs (pow
x j)` through `pow_nonneg` and never prove `|xʲ| ≤ rʲ` at all.

## Decision

### 1. The radius is carried as data, not defined as a supremum

`CReal.powerSeriesCauchyWithinRadius` takes `R` as an ordinary parameter with a
weighted coefficient bound `∀ k, |a k| · Rᵏ ≤ M`, and expresses "`x` is strictly
inside the radius" as a caller-supplied ratio `r` together with `0 ≤ r`, `r < 1`
and `le (abs x) (mul r R)`.

This is the same decision `geometric.rs` already records for `PosBound (1 − x)
k`, and it is forced by the same fact. A proof needs a ratio it can *compute
with* — one it can raise to the `k`-th power and hand to a geometric bound. A
bare `lt (abs x) R` is an `Exists` over a rational gap; extracting a usable
ratio from it is a further elimination that a `Prop`-valued target cannot always
perform, and nothing manufactures one from `|x| < R` in general. Defining the
radius as a supremum is strictly worse again: it needs the least-upper-bound
principle over a set that is not located.

A caller who has `|x| < R` in the ordinary sense supplies `r` themselves; this
asks for nothing they do not already have, which is precisely the argument
`cancellation.rs` makes for its own `PosBound` parameters.

`le zero R` is deliberately **not** a hypothesis. The derivation consumes only
`0 ≤ rᵏ`, which follows from `0 ≤ r` alone, so requiring `0 ≤ R` would weaken
the theorem for nothing.

### 2. `abs_pow_le` is the one genuinely new general fact

`CReal.abs_pow_le : ∀ x b, le (abs x) b → ∀ k, le (abs (pow x k)) (pow b k)`.

A radius is a statement about `|x| < R`, so `x` may be negative and
`powerSeriesTerm_abs_le`'s `0 ≤ x` dodge is unavailable. The proof is `Nat.rec`
on `k` and the step is a *single* application of
`CReal.abs_mul_le_of_bounds`: `pow`'s ι-reduction already identifies `pow x
(Nat.succ j)` with `mul (pow x j) x`, so the goal is definitionally that lemma's
conclusion and the inductive hypothesis plus the outer `le (abs x) b` are
exactly its two premises. No case split on a sign occurs anywhere.

The base case is the only awkward part, and only because this kernel has no
`CReal.abs_one`: `le (abs one) one` is assembled from `zero_lt_one` through
`neg_le_neg` and `series.rs`'s `neg_zero_equiv`, then `abs_le`.

### 3. The instances are proved `Equiv`s, and the lane measured that rather than asserting it

`CReal.expSeriesPartial` is `CReal.sumRange CReal.expTerm` — the exponential
series *at the point 1*. So the instance statement is `Equiv (expSeriesPartial
n) (powerSeriesPartial expTerm one n)`, and the question the brief asks is
whether that is `Eq.refl` or a proof.

It is a proof. `powerSeriesPartial` multiplies each coefficient by `pow one k`,
and while `pow one Nat.zero` ι-reduces to `one`, `mul (expTerm 0) one` does not
reduce to `expTerm 0` — `CReal.mul`'s representative resamples its factors, so
`mul_one` is a proved `Equiv` and never a reduction. This is asserted nowhere:
`power_series_tests.rs::exp_instance_is_a_proved_equiv_because_the_sides_are_not_def_eq`
runs `def_eq_in` on the two sides at the concrete `n = 1` and requires it to
come back **false**, then requires the theorem to land on the `Equiv`. If the
sides were ever made definitionally equal, that test fails and says so.

The `Equiv` itself is `sum_range_congr` against `CReal.one_pow : ∀ k, Equiv (pow
one k) one` (also new, also a `Nat.rec` induction) and `mul_one`.

## Consequences

- The next lane on this ladder should start from `CReal.powerSeriesPartial` and
  the two radius theorems, not from the comparison test, which is done.
- Deliverable 4 (termwise addition and scalar multiples inside a common radius)
  is not blocked by anything this lane found; `CReal.sumRange_add` and
  `CReal.mul_sumRange` are both already declared, and the shape of the work is
  a congruence over `powerSeriesPartial` rather than new analysis.
- The quotient form of the geometric closed form remains open, and is not hard:
  `geometric.rs::declare_geom_tail_bounded_div` already shows the route
  (multiply through by `inv (1 − x) k h` and cancel), so a
  `geom_closed_form_div` taking the same `PosBound` witness is a short
  derivation from `mul_sub_one_geom`. It is recorded here rather than landed
  because this lane spent its budget on the radius.
- The radius statement's hypothesis order is shared between the `Cauchy` and
  `Converges` forms through one `RadiusFrame`, so the two cannot drift apart.
