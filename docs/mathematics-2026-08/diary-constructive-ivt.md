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
