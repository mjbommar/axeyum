# Spivak Chapter 7: bisection is enough, and trisection was never the point

**2026-08-25.** `CReal.ivt_step` landed — the one-step bracket lemma for the
constructive Intermediate Value Theorem. The proof is **simpler than the
textbook constructive argument**, and the reason is worth writing down because
it generalizes.

## The setup

The classical IVT — `f` continuous on `[a,b]`, `f a ≤ 0 ≤ f b` ⟹ `∃x, f x = 0`
— is **not constructively provable.** It asserts a root you can compute, and the
root's position can be made to depend on an undecidable comparison. Bishop's
replacement is the **approximate** IVT: `∀ε > 0, ∃x ∈ [a,b], |f x| ≤ ε`.

The obstruction to naive bisection is precise: to choose a half you must decide
`f(mid) < 0` or `f(mid) > 0`, and `CReal` order is undecidable — no Markov
principle, and `Apart` is an `Or` whose `Or.rec` does not eliminate into `Type`.

The standard fix in the literature is **trisection with an overlap**: compare
`f` at two interior points `u < v`, so cotransitivity is applied to a pair that
is *strictly separated by construction*, and the bracket shrinks by a worst-case
factor of 2/3.

## What the lane found instead

Trisection is needed only to maintain the **exact** invariant `f P ≤ 0 ≤ f Q`.
That invariant offers no fixed strict pair to pivot `lt_cotrans` on, so the
strictness has to be manufactured from two interior sample points.

But the approximate IVT is going to give up exactness anyway. So weaken the
bracket invariant to carry the slack from the start:

```text
f P ≤ ε        and        −ε ≤ f Q
```

Now `−ε < ε` is a **fixed, always-strict pair** — strict because `ε > 0`, and
strict *independently of `P`, `Q`, `f`, and the midpoint*. Apply
`CReal.lt_cotrans` to that pair at `z := f m` and it returns
`(−ε < f m) ∨ (f m < ε)` **unconditionally**. Either disjunct preserves the
invariant on a half-width bracket:

```text
f m < ε   ⟹  take [m, Q]
−ε < f m  ⟹  take [P, m]
```

**Ordinary midpoint bisection, no interior sample pair, no case split on any
exact sign, and the bracket halves rather than shrinking by 2/3.**

## The generalizable point

Cotransitivity needs a strict pair to pivot on. Trisection *constructs* one out
of the function's own values, which is expensive and forces two evaluations.
The slack in an approximate statement *already contains* one, for free, in the
constants — and it is available before you look at the function at all.

So: **when a constructive argument seems to need extra sample points to create
strictness, check whether the statement's own error tolerance already provides
it.** The tolerance is a strict pair sitting in plain sight.

This is a case where the constructive proof came out *shorter and with a better
constant* than the classical route it replaces, which is not the usual
direction.

## What is landed and what is not

- **`CReal.ivt_step`** — the one-step lemma, fully general in `F, P, Q, ε`,
  axiom-free, instantiated at `f := id` on the asymmetric bracket `[0,1]` with
  all four hypotheses genuinely discharged.
- **`CReal.ivt_approx` is open.** It needs `ivt_step` iterated `N` times by a
  primitive recursion carrying the six-part invariant, with `N` chosen from
  `Nat.pow_lt_pow_of_lt` (landed earlier the same day, for an unrelated
  number-theory target) and the Archimedean property against the width the
  modulus supplies. That is a new indexed recursive construction, not a
  continuation of this one.

Chapter 7's other two theorems remain genuinely unavailable: **EVT** asserts an
*attained* maximum, and boundedness holds for **uniformly** continuous functions
— which is why `UniformlyContinuousOn`, not pointwise continuity, is the
hypothesis Chapters 13 and 14 run on here.

---

## Addendum: `ivt_approx` and the geometric series are blocked on ONE lemma

`CReal.ivt_iter` landed — `ivt_step` iterated `N` times by structural `Nat`
induction, carrying the six-part invariant against the *original* endpoints
while `ivt_step`'s own slots track the current bracket. Two details worth
keeping:

- The width recursion needed **no `pow_succ`/`pow_zero`**: `pow`'s own `Nat.rec`
  ι-reduces `pow half (succ j)` to `mul (pow half j) half` definitionally, so
  the step only needs `mul_assoc`.
- `N` comes from `Nat.size(M)` via the existing **`Nat.lt_pow_size`**, which
  supplies the existence witness directly — cheaper than the
  `Nat.pow_lt_pow_of_lt` route I suggested.

**What blocks `ivt_approx` is not IVT-specific.** The lane named it:

> a quantitative bound relating `pow x n` (`0 ≤ x < 1`) to a `natDivSucc`-shaped
> rational threshold — e.g. `pow half n ≤ ofRat (natDivSucc 1 n)` — to turn "`N`
> large enough that `2^N ≥ M`" (Nat-level, solved) into "`width_N` small enough"
> (`CReal`-level).

**That is the same lemma the geometric series needs**, and the same one
`power.rs`'s own doc calls "the geometric-decay-dominates-harmonic-rate estimate
this development does not yet build."

And it **already exists over ℚ**. `Rat.bernoulli_harmonic_bound` says
`(1 + m·t)·xᵐ ≤ 1`; at `x = 1/2, t = 1` that is exactly
`(1/2)ᵐ ≤ 1/(1+m) = natDivSucc 1 m`.

So three separate Spivak chapters — **7** (IVT), **13→18** (exp), **22–23**
(series) — are blocked on transporting one rational inequality across the
`CReal.pow` sampling schedule. The hazard there, flagged before anyone builds
it: **`CReal.mul` does not sample its arguments at the index it is sampled at**,
so `seq (pow x a) b` is *not* `Rat.pow (seq x b) a`, and the bridge may only be
an inequality with slack. Slack is fine — every consumer is a bound.

This is the fourth time in this session that separate developments turned out to
need one missing lemma, and the third time nobody could see it from inside a
single lane.

---

# `CReal.ivt_approx` is closed

**2026-08-25.** Spivak Chapter 7's Intermediate Value Theorem, in the form this
logic admits:

```text
CReal.ivt_approx :
  ∀ F a b, UniformlyContinuousOn F a b → le a b →
           le (F a) zero → le zero (F b) →
  ∀ e, ∃ x, le a x ∧ le x b ∧ le (abs (F x)) (ofRat (natDivSucc 1 e))
```

Kernel-checked, axiom-free, `creal_prelude_builds` observed passing. Four lanes:
`ivt_step` (the bisection insight), `ivt_iter` (the iteration), the decay bound
`pow_half_le_natDivSucc`, and the assembly.

## A correction to this note's own arithmetic

An earlier version of the estimate here — and the brief built from it — said
`e := 9` gives `eps = 1/20`, continuity index `19`, and "`2^N ≥ 20`, so
`N = 5`."

**That was wrong, and it was wrong in a way worth recording.** It assumed an
*exponential* bound `pow(1/2, N) ≤ 1/2^N`. The lemma that actually landed,
`pow_half_le_natDivSucc`, is **linear**: `pow(1/2, N) ≤ 1/(N+1)`. The two agree
only at small `N` and diverge fast, so a depth computed from the exponential
form is far too small.

The corrected depth is `bisect_n := M·delta + c`, with `c := CReal.bound (b−a)`
and `M := c+1` — chosen so `M · natDivSucc(1, bisect_n) = natDivSucc(1, delta)`
is an **equality**, via `Rat.natDivSucc_scale`'s own `(c+1)·m + c` index shape,
rather than merely a bound. No search and no `Exists.rec`, because `CReal.bound`
is a total computable projection.

The lesson is narrow but sharp: **an estimate carried forward from a lane's
report is only valid against the lemma that lane was imagining.** I propagated
`N = 5` into a brief without re-checking it against the bound that had since
landed under a different shape. The lane caught it and declined to assert a
concrete numeral it could not evaluate, documenting the formula instead — which
is the right call.

## Also worth keeping, from the assembly

- `n := succ (2·e)` makes `sgn_eps + sgn_eps ~ ofRat (natDivSucc 1 e)` an
  **exact equality** via `natDivSucc_add` then `natDivSucc_halve` — the same
  no-weakening trick the derivative-uniqueness proof found independently.
- Two rejections, both ~10–20 s (ordinary type errors, per the diagnostic):
  `erefl` (Equiv reflexivity) used where `le_refl` was needed, at three sites;
  and an `abs_le` slot wanting `le (neg (F q)) target` where the
  mathematically-equivalent-but-syntactically-different `le (neg target) (F q)`
  had been built. **Neither was an argument-order defect** — that makes four
  rejections today whose cause was *not* the thing the prior predicted.

## What this unblocks

`docs/mathematics-2026-08/diary-apart-as-data.md` records that exact
`lt`-reflection, Chapter 12's inverse function theorem, and **tightness of
apartness** are one problem in three guises, all waiting on an exact IVT
preimage. `ivt_approx` is the *approximate* preimage; whether it suffices for
those three, or whether they need the exact form, is now the live question.
