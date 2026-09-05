# Lane: incidence-geometry — synthetic incidence geometry as a record, with the coordinate plane as a model (W3-8)

<!-- plan-section: lane-status -->

**Your lane's block (`IN PROGRESS`, incidence-geometry, 2026-09-05).** W3-8's
record landed and is green; the rational model and the `ring::rat` capability
it forced are in the same branch. `Geo.Incidence` is a **21-field record over
two carriers**, declared through the ADR-1578 `declare_record` spine at
`Sort 2` with the ADR-1595 setoid discipline — each carrier its own
equivalence, the incidence relation a congruence field for each, no `funext`
and no `Quot.sound`
([ADR-1635](../../research/09-decisions/adr-1635-incidence-geometry-needs-apartness-in-exactly-one-axiom-and-the-rational-ring-normalizer-could-not-cancel.md)).
All of it in NEW files (`crates/axeyum-lean-kernel/src/geo.rs`,
`src/geo/qplane.rs`) registered from `lib.rs`, so a concurrent lane's merge
into the kernel stays additive; `creal_point.rs` was not touched at all.

**The finding the brief asked for: exactly one axiom needs apartness.**
Hilbert I.1's uniqueness half (`joinUnique`) is the only axiom that *consumes*
distinctness; `joinExists`, `twoPoints` and `triangle` only produce it. Over ℚ
the consumption is a field cancellation and `(P = Q) → False` supplies it; over
ℝ the consumption is a division by `distSq P Q`, which is `CReal.inv`, which is
`PosBound`-indexed — the wall `CPoint.collinear_of_area_zero` already
documents in its own doc comment. So `apart` is a **field** of the record with
three laws (`apartNe`, `apartSymm`, `apartCongr`), and each model supplies its
own notion. `apartNe` is what stops the abstraction being vacuous: without it
`apart := True` satisfies every axiom.

**The unbudgeted cost was not the geometry, it was the producer.**
`ring::rat` declined *every* coordinate identity in this lane, for two
independent reasons neither of which was visible before the goals were put to
it:

1. It had no `cancel_pairs`. Its module doc said, verbatim, "None of the five
   ℚ targets produce an `x + (-x)` summand pair, so it was not built." Every
   identity here produces nothing else — each one asserts that a determinant
   expansion collapses.
2. It had no way to drop a `Num(0)`. `scale_item` emits `Item::Num(0)` for
   every `x * 0` and the additive normalizer never merges two `Num`s, so
   `a*0 + b*0 + c` normalized to three items against `c`'s one. Every
   statement about the triangle `(0,0), (1,0), (0,1)` has that shape.

Both passes are now in `ring::rat::Problem::cancel_pairs` (the first ported
from `ring::int`, the second new), with three matched tests including a
negative control (`x*y + -(x*x) = 0` must still decline `NotAnIdentity`) that
dies if the pass stops comparing factor lists. This is the ADR-0601 shape: the
geometry did not get a bespoke proof, the producer got a capability, and the
capability is guarded by a control that can fail.

**What the ℚ model costs, and where.** The whole model factors through ONE
algebraic lemma, `Geo.QPlane.onPivot`, and the `a ≠ 0 ∨ b ≠ 0` case split uses
it in *both* branches (the `b` branch is the same lemma with `(u,v,s,t)` and
`(U,V)` swapped, so the second case is three `ring` rearrangements rather than
a second proof). `Geo.QPlane.joinProp` — every line through `P` and `Q` is
proportional to the explicit join — needs **no non-degeneracy hypothesis at
all**; the three relations are three unconditional ring identities with the two
incidence left-hand sides added as summands on either side, and all three were
verified by hand before being encoded. Distinctness is spent in exactly one
place, `Geo.QPlane.joinNondeg`. `twoPoints` needs the case split only for the
FIRST point: the second is the first plus the direction `(-b, a)`, whose
incidence is one ring identity and whose apartness needs `Nondeg` alone —
`Rat.inv` appears exactly once in the whole model, in `Geo.QPlane.basePoint`.

**Line equality is extensional and that is the load-bearing choice.** With
`Equiv l m := ∀ P, (on P l → on P m) ∧ (on P m → on P l)`, reflexivity,
symmetry and transitivity are free and `onLine` is an `And.left`. The
alternative — proportionality of coefficient triples — needs the nonzero case
split three times just for transitivity, once per conjunct.

**What did NOT land: the ℝ² instance.** It is a `Geo.Incidence` instance and
not a parallel development, which is the point of the record, but nothing of it
is written. The sized obstruction is `joinUnique`, and only `joinUnique`:
`CPoint.collinear_of_area_zero` (`∀ A B C k, PosBound (distSq A B) k →
Equiv (cross A B C) zero → Collinear A B C`) is the theorem it has to route
through, and it takes a `PosBound` witness, so `apart P Q` for the ℝ model has
to be `∃ k, PosBound (distSq P Q) k` and the ℝ analogue of `Geo.QPlane.onPivot`
has to consume that witness through `CReal.inv` rather than through
`Rat.mul_eq_zero`. The other three axioms are cheaper than their ℚ twins, not
harder: `joinExists` is the same coordinate computation over `CReal.Equiv`,
`twoPoints` is the same shift, and `triangle` has `CPoint.cross_self_left` and
`CPoint.NonCollinear` already built. Nothing about the record blocks it.

<!-- plan-section: landed-changes -->

| 2026-09-05 | `7ec964eab` | `Geo.Incidence` — a 21-field incidence record over two carriers with Hilbert I.1 (split into `joinExists`/`joinUnique`, this kernel having no `ExistsUnique`), I.2 and I.3, plus `apart` and its three laws; and five theorems derived once over an arbitrary `I : Geo.Incidence` — `Collinear` (a Definition), `collinear_intro`, `collinear_perm`, `distinct_lines_meet_once` (which IS "two distinct lines meet in at most one point") and `triangle_not_collinear`. 7 tests. Every one of the 29 names is asserted present AND axiom-free with `Environment::contains` checked FIRST, and the declaration list is derived from `RecordNames::field_count` rather than a literal. |
