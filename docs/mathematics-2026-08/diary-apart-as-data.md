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
