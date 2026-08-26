# `Apart` as data: when a case split is legitimate

**2026-08-25.** A lane working Spivak Chapter 12 drew a distinction sharp enough
to be worth stating on its own, because it recurs everywhere in this
development and is easy to get backwards.

## The rule

> **Case-splitting on a *given* disjunction is valid. It is not excluded middle
> on an undecidable proposition.**

`CReal.Apart x y` is an `Or`. If a caller *hands you* `Apart x y`, you may
eliminate it and reason in both branches — that is ordinary `Or.rec` into
`Prop`, sanctioned and constructive. What you may **not** do is *derive*
`Apart x y` from nothing, or from `¬ Equiv x y`; that is the undecidability.

So the same syntactic move is legitimate or forbidden depending entirely on
where the disjunction came from. This is the constructive analogue of the
distinction between *having* a witness and *asserting one exists*.

## The instance

Chapter 12 wants order reflection: a strictly increasing `F` satisfies
`F x < F y → x < y`.

**Unconditionally, this is not provable here.** Getting `x < y` out of
`F x < F y` requires *deciding* which of `x < y`, `y < x` holds, and `CReal.lt`
is undecidable. Every route the lane traced either silently assumed a domain
order to get started, or needed an exact localisation step.

**With `Apart x y` supplied as data, it is immediate**: one branch is the goal;
the other is refuted by `strict_mono_of_pos_deriv` composed with `lt_trans` and
`lt_irrefl`. That is `CReal.order_reflect_of_pos_deriv`, landed.

## The structural characterisation, which is the useful part

> **Exact order-reflection is precisely as hard as an exact IVT preimage, and
> for the same reason: both convert a codomain fact into domain position
> information.**

That is why Chapter 12's inverse function theorem sits behind Chapter 7's
`ivt_approx`, and why `ivt_approx` sitting behind a `pow`-vs-`natDivSucc` decay
bound blocks *both* chapters. It also predicts which other Chapter 12 statements
will be reachable: anything that only needs order *preservation* (a domain fact
becoming a codomain fact) is fine; anything reflecting is not, absent an
apartness witness or an exact IVT.

## What this does not license

`Apart`'s `Or` **does not eliminate into `Type`**. So a case split on given
apartness proves `Prop`s and cannot *construct* data — you cannot build the
inverse *function* this way, only prove properties of pairs already known apart.
The inverse as a construction still waits on the exact preimage.

Related: `CReal.lt_cotrans` is the other sanctioned route, and it is different in
kind — it *manufactures* a disjunction from a strict pair rather than consuming
a supplied one, which is why the constructive IVT can use it where bisection
alone fails. See
[`diary-constructive-ivt.md`](diary-constructive-ivt.md).

---

## Addendum: tightness of apartness is the same wall, a third time

A lane asked whether a strictly monotone `F` reflects **`Equiv`** —
`Equiv (F x) (F y) → Equiv x y` — hoping it might be reachable where `lt`
reflection is not, since `Equiv` looks like a negative statement.

**Half of it is free, and the half that is not is the same wall.**

From `h : Equiv (F x) (F y)`, assume `Apart x y`; `strict_injective_of_pos_deriv`
gives `Apart (F x) (F y)`, which contradicts `h` via `not_equiv_of_apart`. So

    Not (Apart x y)

**is** constructively derivable — proving a negation needs no case split and no
excluded middle. The blocker is the next step: turning `Not (Apart x y)` into
`Equiv x y` requires **tightness of apartness**, and this development has only
the easy direction. A lane checked every `NameId` field in `creal.rs` and found
`not_equiv_of_apart : Apart x y → Not (Equiv x y)` and no converse.

That absence is not an oversight. **Tightness is `lt`-reflection in `Equiv`'s
clothing**: a codomain non-apartness fact would have to yield domain positional
information, with no bisection available to produce it.

So three statements that look independent are one problem:

| Statement | Blocked on |
|---|---|
| exact `lt` reflection (`F x < F y → x < y`) | domain position from a codomain fact |
| exact inverse function theorem (Ch 12) | an exact IVT preimage |
| tightness (`¬ Apart x y → Equiv x y`) | the same, in `Equiv`'s clothing |

All three wait on `ivt_approx`. That is worth knowing before anyone attempts
them separately — and it is the fourth time in this session that separate
reports turned out to describe one cause.

**What IS reachable, and landed**: everything *preserving*.
`strict_antitone_of_neg_deriv` (the mirror, via `neg ∘ F`), and
`strict_mono_comp` — composition of strictly increasing maps. The composition
one carries a finding worth keeping: **`hasDerivative_chain` does not supply its
hypothesis cheaply**, because the chain rule fixes ONE shared interval `[a,b]`
for both functions via a self-map hypothesis, which would force `G` strictly
increasing on `F`'s *domain* rather than on `F`'s *range* — not the composition
Chapter 12 wants. Stating the corollary over the strict-monotonicity
*conclusions*, plus an explicit range hypothesis, makes it pure function
application with no derivative machinery at all.
